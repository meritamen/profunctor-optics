import Data.Functor.Constant
import Data.List

class Profunctor p where
  dimap :: (a -> b) -> (c -> d) -> p b c -> p a d

  lmap :: (a -> b) -> p b c -> p a c
  lmap f = dimap f id

  rmap :: (c -> d) -> p a c -> p a d
  rmap f = dimap id f

instance Profunctor (->) where
  dimap f g h = g . h . f 

class Profunctor p => Cartesian p where
  first  :: p a b -> p (a, c) (b, c)
  second :: p a b -> p (c, a) (c, b)

instance Cartesian (->) where
  first f (a, c) = (f a, c)
  second f (c, a) = (c, f a)

class Profunctor p => Cocartesian p where
  left  :: p a b -> p (Either a c) (Either b c)
  right :: p a b -> p (Either c a) (Either c b)

instance Cocartesian (->) where
  left  f = either (Left . f) Right
  right f = either Left (Right . f)

class Profunctor p => Monoidal p where
  par :: p a b -> p c d -> p (a, c) (b, d)
  empty :: p () ()

instance Monoidal (->) where
  par f g (a, c) = (f a, g c)
  empty = id

newtype UpStar f a b = UpStar { runUpStar :: a -> f b }

instance Functor f => Profunctor (UpStar f) where
  dimap f g (UpStar h) = UpStar $ fmap g . h . f

instance Functor f => Cartesian (UpStar f) where
  first (UpStar f) = UpStar $ \(a, c) -> (,c) <$> f a
  second (UpStar f) = UpStar $ \(c, a) -> (c,) <$> f a

instance Applicative f => Cocartesian (UpStar f) where
  left (UpStar f) = UpStar $ either (fmap Left . f) (fmap Right . pure)
  right (UpStar f) = UpStar $ either (fmap Left . pure) (fmap Right . f)

instance Applicative f => Monoidal (UpStar f) where
  par (UpStar f) (UpStar g) = UpStar $ \(a, c) -> (,) <$> f a <*> g c
  empty = UpStar $ pure . id

newtype DownStar f a b = DownStar { runDownStar :: f a -> b }

instance Functor f => Profunctor (DownStar f) where
  dimap f g (DownStar h) = DownStar $ g . h . fmap f

newtype Tagged a b = Tagged { unTagged :: b }

instance Profunctor Tagged where
  dimap _ g (Tagged b) = Tagged $ g b

instance Cocartesian Tagged where
  left (Tagged b) = Tagged $ Left b
  right (Tagged b) = Tagged $ Right b

instance Monoidal Tagged where
  par (Tagged b) (Tagged d) = Tagged (b, d)
  empty = Tagged ()

data Adapter s t a b = Adapter { from :: s -> a, to :: b -> t }

type AdapterP s t a b = forall p. Profunctor p => p a b -> p s t

adapterC2P :: Adapter s t a b -> AdapterP s t a b
adapterC2P (Adapter f t) = dimap f t

from' :: AdapterP s t a b -> s -> a
from' ad = getConstant . runUpStar (ad (UpStar Constant))

to' :: AdapterP s t a b -> b -> t
to' ad = unTagged . ad . Tagged

shift :: Adapter ((a, b), c) ((a', b'), c') (a, (b, c)) (a', (b', c'))
shift = Adapter f t
  where
    f ((a, b), c) = (a, (b, c))
    t (a', (b', c')) = ((a', b'), c')

shift' :: AdapterP ((a, b), c) ((a', b'), c') (a, (b, c)) (a', (b', c'))
shift' = dimap assoc assoc'
  where
    assoc  ((x, y), z) = (x, (y, z))
    assoc' (x, (y, z)) = ((x, y), z)

type LensP s t a b = forall p. Cartesian p => p a b -> p s t

data Lens s t a b = Lens { view :: s -> a, update :: (b, s) -> t }

lensC2P :: Lens s t a b -> LensP s t a b
lensC2P (Lens v u) = dimap dup u . first . lmap v
  where
    dup a = (a, a)

view' :: LensP s t a b -> s -> a
view' ln = getConstant . runUpStar (ln (UpStar Constant))

update' :: LensP s t a b -> (b, s) -> t
update' ln (b, s) = ln (const b) s

π1 :: Lens (a, c) (b, c) a b
π1 = Lens v u
  where
    v = fst
    u (b, (_, c)) = (b, c)

π1' :: LensP (a, c) (b, c) a b
π1' = first

data Prism s t a b = Prism { match :: s -> Either a t, build :: b -> t }

type PrismP s t a b = forall p. Cocartesian p => p a b -> p s t

prismC2P :: Prism s t a b -> PrismP s t a b
prismC2P (Prism m b) = dimap m (either id id) . left . rmap b

match' :: PrismP s t a b -> s -> Either a t
match' pr = runUpStar (pr (UpStar Left))

build' :: PrismP s t a b -> b -> t
build' pr = unTagged . pr . Tagged

the :: Prism (Maybe a) (Maybe b) a b
the = Prism (maybe (Right Nothing) Left) Just

the' :: PrismP (Maybe a) (Maybe b) a b
the' = dimap (maybe (Right Nothing) Left) (either Just id) . left

data Affine s t a b = Affine { preview :: s -> Either a t, set :: (b, s) -> t }

type AffineP s t a b = forall p. (Cartesian p, Cocartesian p) => p a b -> p s t

affineC2P :: Affine s t a b -> AffineP s t a b
affineC2P (Affine p st) = dimap preview' merge . left . rmap st . first
  where
    preview' s = either (\a -> Left (a, s)) Right (p s)
    merge = either id id

preview' :: AffineP s t a b -> s -> Either a t
preview' af = runUpStar (af (UpStar Left))

set' :: AffineP s t a b -> (b, s) -> t
set' af (b, s) = af (const b) s

maybeFirst' :: AffineP (Maybe a, c) (Maybe b, c) a b
maybeFirst' = first . dimap (maybe (Right Nothing) Left) (either Just id) . left

maybeFirst'' :: AffineP (Maybe a, c) (Maybe b, c) a b
maybeFirst'' = π1' . the'

data Traversal s t a b = Traversal { content :: s -> [a], fill :: ([b], s) -> t }

type TraversalP s t a b = forall p. (Cartesian p, Cocartesian p, Monoidal p) => p a b -> p s t

traversalC2P :: Traversal s t a b -> TraversalP s t a b
traversalC2P (Traversal c f) = dimap dup f . first . lmap c . ylw
  where
    ylw h = dimap (maybe (Right []) Left . uncons) merge $ left $ rmap cons $ par h (ylw h)
    cons = uncurry (:)
    dup a = (a, a)
    merge = either id id

contents' :: TraversalP s t a b -> s -> [a]
contents' tr = getConstant . runUpStar (tr (UpStar (\a -> Constant [a])))

firstNSecond :: Traversal (a, a, c) (b, b, c) a b
firstNSecond = Traversal c f
  where
    c (a1, a2, _)  = [a1, a2]
    f (bs, (_, _, x)) = (head bs, (head . tail) bs, x)

firstNSecond' :: TraversalP (a, a, c) (b, b, c) a b
firstNSecond' pab = dimap group group' (first (pab `par` pab))
  where
    group  (x, y, z) = ((x, y), z)
    group' ((x, y), z) = (x, y, z)
