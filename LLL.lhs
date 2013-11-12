> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module LLL where

> import Data.Foldable
> import Data.Traversable

> data Exp x
>   = Exp x :$ [Exp x]
>   | Tup [Exp x]
>   | Splay (Exp x)
>   | Con  Bit
>   | In   Int
>   | Def  x
>   deriving (Show, Functor, Foldable, Traversable)

> instance Monad Exp where
>   return = Def
>   Def x >>= k = k x
>   (f :$ as) >>= k = (f >>= k) :$ map (>>= k) as
>   Tup es >>= k = Tup (map (>>= k) es)
>   Splay e >>= k = Splay (e >>= k)
>   Con b >>= k = Con b
>   In i >>= k = In i

> type Prog f x = ([([f], Exp x)],[Exp x])

> data Val
>   = VB [Bit]
>   | VT [Val]
>   | VF String ([Val] -> [Val])

> data Bit = BU | B0 | B1 deriving Eq
> instance Show Bit where
>   show BU = "#"
>   show B0 = "0"
>   show B1 = "1"

> instance Show Val where
>   show (VB bs) = bs >>= show
>   show (VT vs) = "(" ++ (vs >>= show) ++ ")"
>   show (VF s _) = s

> zipw :: (a -> b -> c) -> [a] -> [b] -> [c]
> zipw f [] _ = []
> zipw f (x : xs) ~(v : vs) = f x v : zipw f xs vs

> oxford :: (Show x, Eq x) => [(x, Val)] -> Prog x x -> [Val] ->[Val]
> oxford gevs (defs, es) ivs = es >>= eval where
>   levs = defs >>= \ (ns, e) -> zipw (,) ns (eval e)
>   evs = levs ++ gevs
>   -- eval :: Exp x -> [Val] -- grr
>   eval (In i)     = [ivs !! i]
>   eval (Def x)    = case lookup x evs of
>     Just v -> [v]
>     _ -> error $ "what's " ++ show x ++ "?"
>   eval (f :$ es)  = eval f $$ (es >>= eval)
>   eval (Tup es)   = [VT (es >>= eval)]
>   eval (Splay e)  = vs where [VT vs] = eval e
>   eval (Con b)    = [VB (repeat b)]
>   ($$) :: [Val] -> [Val] -> [Val]
>   ~[~(VF _ f)] $$ vs = f vs

> andy :: [Val] -> [Val]
> andy ~[~(VB xs), ~(VB ys)] = [VB (zipw (*) xs ys)] where

> noty :: [Val] -> [Val]
> noty ~[~(VB xs)] = [VB (map naw xs)] where
>   naw BU = BU
>   naw B0 = B1
>   naw B1 = B0

> xory :: [Val] -> [Val]
> xory ~[~(VB xs), ~(VB ys)] = [VB (zipw (+) xs ys)] where

> dint :: [Val] -> [Val]
> dint ~[~(VB xs)] = [VB (B0 : xs)]

> dexp :: [Val] -> [Val]
> dexp ~[~(VB cs), ~(VB bs)] = [VB (go B0 cs B0 B0 bs)] where
>   go B0 (B1 : cs) o d (b : bs) = o : go B1 cs o b bs
>   go B1 (B0 : cs) o d (b : bs) = d : go B0 cs d d bs
>   go _ (c : cs) o d (b : bs) = o : go c cs o d bs
>   go _ _ _ _ _ = []

> srff :: [Val] -> [Val]
> srff ~[~(VB cs), ~(VB ss), ~(VB rs)] = [VB (go B0 cs B0 (B0, B0) ss rs)]
>   where
>     go c cs q sr ss rs = q : mo c cs q sr ss rs
>     mo B0 (B1 : cs) q _ (s : ss) (r : rs) = go B1 cs q (s, r) ss rs
>     mo B1 (B0 : cs) q sr (_ : ss) (_ : rs) = go B0 cs q' sr ss rs where
>       q' = case (sr, q) of
>              ((B0, B0), q) -> q
>              ((B1, B0), q) -> B1
>              ((B0, B1), q) -> B0
>              ((B1, B1), q) -> BU
>     mo _ (c : cs) q sr (_ : ss) (_ : rs) = go c cs q sr ss rs
>     mo _ _ _ _ _ _ = []

> clock :: Val
> clock = VB (cycle [B1, B0])

> myGEnv :: [(String, Val)]
> myGEnv =  [  ("and",    VF "and" andy)
>           ,  ("xor",    VF "xor" xory)
>           ,  ("d0c",    VF "d0c" dexp)
>           ,  ("csr",    VF "csr" srff)
>           ,  ("t0c",    VF "t0c" (oxford myGEnv myT))
>           ,  ("c4",     VF "c4"  (oxford myGEnv myC4))
>           ,  ("clock",  VF "clock" (const [clock]))
>           ]

> myT :: Prog String String
> myT =  (  [  (["d"], Def "xor" :$ [In 1, Def "q"])
>           ,  (["q"], Def "d0c" :$ [In 0, Def "d"])
>           ]
>        ,  [Def "q"]
>        )

> myC4 :: Prog String String
> myC4 = (  [  (["q0"], Def "t0c" :$ [In 0, Con B1])
>           ,  (["q1"], Def "t0c" :$ [Def "q0", Con B1])
>           ,  (["q2"], Def "t0c" :$ [Def "q1", Con B1])
>           ,  (["q3"], Def "t0c" :$ [Def "q2", Con B1])
>           ]
>        ,  [Def "q3", Def "q2", Def "q1", Def "q0"]
>        )

> till :: Int -> Val
> till t = VB [b | i <- [0..t], b <- [B1, B0]]

> control :: [Bit] -> Val
> control bs = VB [b | b <- bs, _ <- [0,1]]

> instance Num Bit where
>   fromInteger 0 = B0
>   fromInteger 1 = B1
>   BU  + _   = BU -- xor
>   _   + BU  = BU
>   b   + b'  | b == b'    = B0
>             | otherwise  = B1
>   BU  * _   = BU -- and
>   _   * BU  = BU
>   B0  * b   = B0
>   B1  * b   = b
>   abs = undefined
>   signum = undefined
