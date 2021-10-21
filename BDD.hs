        module BDD where
import Control.Monad(replicateM, liftM2)
import qualified Data.IntMap.Strict as M
import Data.IntMap.Strict(IntMap, (!?))
import qualified Data.IntSet as S
import Data.IntSet(IntSet)
import Data.List(partition, foldl', sort)
import Test.QuickCheck

newtype DAG = DAG (IntMap IntSet)
  deriving (Eq)

instance Arbitrary DAG where
  arbitrary = fmap tc $ sized dag where
    dag :: Int -> Gen (IntMap IntSet)
    dag 0 = return (M.singleton 0 S.empty)
    dag n = do
      d <- dag (n - 1)
      n_edges <- chooseInt (0, n-1)
      edges <- fmap S.fromList $ replicateM n_edges (choose (0, n-1))
      return (M.insert n edges d)

instance Show DAG where
  show (DAG d) = "mkDag " ++ show [(i, S.toList es) | (i, es) <- M.toList d]

mkDag :: [(Int, [Int])] -> DAG
mkDag ns = tc (M.fromList [(i, S.fromList es) | (i, es) <- ns])

-- Transitive closure (input is reflexively closed)
tc :: IntMap IntSet -> DAG
tc is = DAG (foldl' tcn M.empty (M.toAscList is)) where
  tcn :: IntMap IntSet -> (Int, IntSet) -> IntMap IntSet
  tcn acc (i, i_edges) =
    M.insert i (S.insert i (S.unions (i_edges : [ tcs | c <- S.toList i_edges, Just tcs <- [acc!?c]]))) acc

data Relatedness = Subtype | Disjoint | MayIntersect
  deriving (Eq, Show)

-- Relate
tr :: DAG -> Int -> Int -> Relatedness
tr d a b | a > b = tr d b a
tr d a b | a == b = Subtype
tr (DAG d) a b =
  case (d!?a, d!?b) of
    (_, Nothing) -> Disjoint
    (_, Just bs) | S.member a bs -> Subtype
    (Just as, Just bs)
        | S.disjoint as bs -> Disjoint
        | otherwise -> MayIntersect
    _ -> Disjoint

prop_dag_refl :: DAG -> Int -> Bool
prop_dag_refl d n = tr d n n == Subtype

prop_dag_symm :: DAG -> Int -> Int -> Bool
prop_dag_symm d a b = tr d a b == tr d b a

prop_dag_trans :: DAG -> NonNegative Int -> NonNegative Int -> NonNegative Int -> Bool
prop_dag_trans d (NonNegative a) (NonNegative b) (NonNegative c) =
  let [aa, bb, cc] = sort [a, b, c] in
  case (tr d aa bb, tr d bb cc, tr d aa cc) of
    (Subtype, Subtype, d) -> d == Subtype
    (MayIntersect, MayIntersect, d) -> True
    (Subtype, MayIntersect, d) -> True
    (MayIntersect, Subtype, d) -> d /= Disjoint
    (Disjoint, Subtype, d) -> True
    (Subtype, Disjoint, d) -> d == Disjoint
    (Disjoint, MayIntersect, d) -> True
    (MayIntersect, Disjoint, d) -> d == Disjoint || d == MayIntersect
    (Disjoint, Disjoint, d) -> True

pdt d (NonNegative a) (NonNegative b) (NonNegative c) =
  let [aa, bb, cc] = sort [a, b, c] in
  case (tr d aa bb, tr d bb cc, tr d aa cc) of
    (Subtype, Disjoint, d) -> property (d == Disjoint)
    _ -> property Discard

------------------------------------------------------------

data BDD = Bot | Select Int BDD BDD | Top
  deriving (Eq, Show)

instance Arbitrary BDD where
  arbitrary = sized bdd where
    bdd :: Int -> Gen BDD
    bdd n | n <= 0 = oneof [return Bot, return Top]
    bdd n = do
      t <- chooseInt (-2, n-1) >>= bdd
      e <- chooseInt (-2, n-1) >>= bdd
      return (select (n-1) t e)

select :: Int -> BDD -> BDD -> BDD
select i t e
  | t == e = e
  | otherwise = Select i t e

type TR = DAG

root :: BDD -> Int
root (Select i _ _) = i
root _ = 0

bdd_contains_exact :: TR -> BDD -> Int -> Bool
bdd_contains_exact trd Top i = True
bdd_contains_exact trd Bot i = False
bdd_contains_exact trd (Select n t e) i =
  case tr trd n i of
    Subtype | n >= i -> bdd_contains_exact trd t i
    _ -> bdd_contains_exact trd e i

bdd_exacts :: TR -> BDD -> (Int -> Bool)
bdd_exacts trd bdd = bdde bdd where
  bdde :: BDD -> (Int -> Bool)
  bdde Top = const True
  bdde Bot = const False
  bdde (Select i t e) = (\j -> if j <= i && tr trd j i == Subtype then bdd_t j else bdd_e j)
    where bdd_e = bdde e
          bdd_t = bdde t

prop_bdd_exact :: TR -> BDD -> NonNegative Int -> Bool
prop_bdd_exact trd bdd (NonNegative i) = bdd_contains_exact trd bdd i == bdd_exacts trd bdd i

rightmost :: BDD -> Bool
rightmost (Select i t e) = rightmost e
rightmost Top = True
rightmost Bot = False

prop_bdd_big :: TR -> BDD -> NonNegative Int -> Bool
prop_bdd_big tr bdd (NonNegative i) = bdd_contains_exact tr bdd (root bdd + i + 1) == rightmost bdd

model :: TR -> BDD -> [Bool]
model tr bdd = map (bdd_exacts tr bdd) [0..root bdd + 1]

model_eq :: TR -> BDD -> BDD -> Bool
model_eq tr a b = meq (model tr a) (model tr b) where
  meq [a] bs = all (a==) bs
  meq as [b] = all (==b) as
  meq (a:as) (b:bs) = a == b && meq as bs

union :: BDD -> BDD -> BDD
union Top _ = Top
union Bot b = b
union _ Top = Top
union a Bot = a
union a@(Select i1 t1 e1) b@(Select i2 t2 e2)
  | i1 > i2 = select i1 (union t1 b) (union e1 b)
  | i1 == i2 = select i1 (union t1 t2) (union e1 e2)
  | otherwise = select i2 (union a t2) (union a e2)

prop_union :: TR -> BDD -> BDD -> Bool
prop_union tr a b = and $ zipWith (\i v -> (bdd_exacts tr a i || bdd_exacts tr b i) == v) [0..] (model tr (union a b))

intersect :: BDD -> BDD -> BDD
intersect Top a = a
intersect Bot _ = Bot
intersect b Top = b
intersect _ Bot = Bot
intersect a@(Select i1 t1 e1) b@(Select i2 t2 e2)
  | i1 > i2 = select i1 (intersect t1 b) (intersect e1 b)
  | i1 == i2 = select i1 (intersect t1 t2) (intersect e1 e2)
  | otherwise = select i2 (intersect a t2) (intersect a e2)

prop_intersect :: TR -> BDD -> BDD -> Bool
prop_intersect tr a b = and $ zipWith (\i v -> (bdd_exacts tr a i && bdd_exacts tr b i) == v) [0..] (model tr (intersect a b))

erase_subtypes :: TR -> Int -> BDD -> BDD
erase_subtypes trd i (Select j t e)
  | j < i && tr trd j i == Subtype = e
  | otherwise = select j (erase_subtypes trd i t) (erase_subtypes trd i e)
erase_subtypes _ _ leaf = leaf

erase_disjoints :: TR -> Int -> BDD -> BDD
erase_disjoints trd i (Select j t e)
  | tr trd j i == Disjoint = e
  | otherwise = select j (erase_disjoints trd i t) (erase_disjoints trd i e)
erase_disjoints _ _ leaf = leaf

prop_erase_subtypes_root :: TR -> BDD -> Property
prop_erase_subtypes_root trd (Select i t e) = property $ model_eq trd (Select i t e) (select i t (erase_subtypes trd i e))
prop_erase_subtypes_root _ _ = property Discard

prop_erase_disjoints_root :: TR -> BDD -> Property
prop_erase_disjoints_root trd (Select i t e) = property $ model_eq trd (Select i t e) (select i (erase_disjoints trd i t) e)
prop_erase_disjoints_root _ _ = property Discard

fully_erase :: TR -> BDD -> BDD
fully_erase trd (Select i t e) = select i (fully_erase trd (erase_disjoints trd i t)) (fully_erase trd (erase_subtypes trd i e))
fully_erase _ leaf = leaf

prop_fully_erase :: TR -> BDD -> Bool
prop_fully_erase tr bdd = model_eq tr bdd (fully_erase tr bdd)

select' :: Int -> Maybe BDD -> Maybe BDD -> Maybe BDD
select' i = liftM2 (select i)

common :: TR -> Int -> BDD -> BDD -> Maybe BDD
common trd c Top Bot = Nothing
common trd c Bot Top = Nothing
common trd c Top Top = Just Top
common trd c Bot Bot = Just Bot
common trd c t@(Select it tt et) e@(Select ie te ee)
  | it > ie && tr trd it c == Subtype = select' it (Just tt) (common trd c et e)
  | it > ie = select' it (common trd c tt e) (common trd c et e)
  | it == ie = select' it (common trd c tt te) (common trd c et ee)
  | it < ie && tr trd ie c == Disjoint = select' ie (Just te) (common trd c t ee)
  | it < ie = select' ie (common trd c t te) (common trd c t ee)
common trd c t@(Select it tt et) e
  | tr trd it c == Subtype = select' it (Just tt) (common trd c et e)
  | otherwise = select' it (common trd c tt e) (common trd c et e)
common trd c t e@(Select ie te ee)
  | tr trd ie c == Disjoint = select' ie (Just te) (common trd c t ee)
  | otherwise = select' ie (common trd c t te) (common trd c t ee)

prop_common_idem :: TR -> BDD -> Bool
prop_common_idem tr bdd =
  case common tr (1 + root bdd) bdd bdd of
    Just bdd2 -> model_eq tr bdd bdd2
    Nothing -> False

prop_common :: TR -> BDD -> Property
prop_common tr (Select i t e) =
  case common tr i t e of
    Just r -> property $ model_eq tr (Select i t e) r
    Nothing -> property Discard
prop_common _ _ = property Discard

prop_common_correct_a :: TR -> BDD -> Bool
prop_common_correct_a tr s =
  common tr c (erase_disjoints tr c s) (erase_subtypes tr c s) /= Nothing
  where c = root s + 1

prop_erase_both_top :: TR -> BDD -> Property
prop_erase_both_top tr s =
  (erase_disjoints tr c s == Top && erase_subtypes tr c s == Top) ==> s == Top
  where c = root s + 1

prop_erase_both_top_s :: BDD -> Property
prop_erase_both_top_s s =
  (erase_disjoints ttr c s == Top && erase_subtypes ttr c s == Top) ==> s == Top
  where c = root s + 1

ttr = mkDag [(0, [0]), (1, [1]), (2, [0, 1, 2]), (3, [1, 3])]

------------------------------------------------------------

qc :: (Testable t) => t -> IO ()
qc = qcs 12

qcs :: (Testable t) => Int -> t -> IO ()
qcs s = quickCheckWith (stdArgs{ maxSuccess = 1000, maxSize = s, maxDiscardRatio = 3 })

main = sequence_ [
    qc prop_common_correct_a,
    qc prop_common_idem,
    qc prop_common,
    qc prop_erase_subtypes_root,
    qc prop_erase_disjoints_root,
    qc prop_fully_erase,
    qc prop_dag_refl,
    qc prop_dag_symm,
    qc prop_dag_trans,
    qc prop_bdd_exact,
    qc prop_bdd_big,
    qc prop_union,
    qc prop_intersect
  ]
