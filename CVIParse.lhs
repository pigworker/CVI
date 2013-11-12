> {-# LANGUAGE DeriveFunctor #-}

> module CVIParse where

> import Control.Monad
> import Control.Applicative
> import Data.Monoid
> import Data.Traversable
> import Data.Char
> import Data.Foldable hiding (elem, sum, all)

> newtype CVIP x = CVIP {cvip :: (Int, String) -> Maybe (x, (Int, String))}
> instance Monad CVIP where
>   return x = CVIP $ \ is -> return (x, is)
>   pa >>= apb = CVIP $ \ is -> do
>     (a, is) <- cvip pa is
>     cvip (apb a) is
> instance Applicative CVIP where
>   pure = return
>   (<*>) = ap
> instance Functor CVIP where
>   fmap = ap . return
> instance Monoid (CVIP x) where
>   mempty = CVIP $ \ is -> mzero
>   mappend p q = CVIP $ \ is -> mplus (cvip p is) (cvip q is)
> instance Alternative CVIP where
>   empty = mempty
>   (<|>) = mappend
> instance MonadPlus CVIP where
>   mzero = mempty
>   mplus = mappend

> eat :: (Char -> Bool) -> CVIP Char
> eat p = CVIP $ \ (i, s) -> case s of
>   c : s | p c -> Just (c, (i + 1, s))
>   _ -> Nothing

> eats :: String -> CVIP ()
> eats s = () <$ traverse (eat . (==)) s

> eol :: CVIP ()
> eol = CVIP $ \ is -> guard (null (snd is)) >> return ((), is)

> col :: CVIP Int
> col = CVIP $ \ is -> return (fst is, is)

> data Extent x = Extent Int (String, x) Int deriving (Show, Eq, Functor)
> pExtent :: CVIP x -> CVIP (Extent x)
> pExtent p = CVIP $ \ is@(i, s) -> do
>   (x, js@(j, _)) <- cvip p is
>   return (Extent i (take (j - i) s , x) j, js)

> data Dir = Up | Dn deriving (Show, Eq)
> data Tile
>   = Wire Dir [(Int, Dir)]
>   | Var String Dir
>   | SplitFrom Dir Int
>   | TupleTo Dir Int
>   | App AppForm
>   | T0 | T1
>   deriving Show
> data AppForm = String :$: [AppForm] deriving Show

> pTile :: CVIP (Extent Tile)
> pTile = pExtent $ fold
>   [  pVar, pSplitFrom, pTupleTo, pWire, pApp
>   ,  T0 <$ eats "0", T1 <$ eats "1"
>   ]

> pDir :: CVIP Dir
> pDir = Up <$ eats "'" <|> Dn <$ eats ","

> pWire :: CVIP Tile
> pWire
>   =    Wire <$> pDir <*> many ((,) <$> (sum <$> many pmp) <*> pDir)
>   <|>  Wire Up [(0, Dn)] <$ eat (`elem` "/|\\")
>   <|>  Wire Up [(1, Dn)] <$ eats "%"
>   <|>  Wire Up [(0, Dn), (0, Dn)] <$ eats "^"
>   where pmp = 0 <$ eats "-" <|> 1 <$ eat (`elem` "/|\\")

> pName :: CVIP String
> pName = (:) <$> eat isLower <*> many (eat isAlphaNum)

> pVar :: CVIP Tile
> pVar
>   =    Var <$> pName <*> pDir
>   <|>  flip Var <$> pDir <*> pName

> spcu :: CVIP ()
> spcu = () <$ many (eat (`elem` " _"))

> pSplitFrom :: CVIP Tile
> pSplitFrom
>   =    do d <- pDir
>           eats ">("
>           ds <- many (spcu *> pDir) <* spcu
>           eats ")"
>           guard (not (elem d ds))
>           return (SplitFrom d (length ds))
>   <|>  do eats "("
>           ds <- many (spcu *> pDir) <* spcu
>           eats ")<"
>           d <- pDir
>           guard (not (elem d ds))
>           return (SplitFrom d (length ds))

> pTupleTo :: CVIP Tile
> pTupleTo
>   =    do d <- pDir
>           eats "<("
>           ds <- many (spcu *> pDir) <* spcu
>           eats ")"
>           guard (not (elem d ds))
>           return (TupleTo d (length ds))
>   <|>  do eats "("
>           ds <- many (spcu *> pDir) <* spcu
>           eats ")>"
>           d <- pDir
>           guard (not (elem d ds))
>           return (TupleTo d (length ds))

> pAppForm :: CVIP AppForm
> pAppForm = (:$:) <$ spcu <*> pName <*> many (spcu *> pArg) <* spcu where
>   pArg = (:$: []) <$> pName <|> id <$ eats "(" <*>pAppForm <* eats ")"

> pApp :: CVIP Tile
> pApp = App <$ eats "[" <*> pAppForm <* eats "]"

> pInterface :: CVIP [Int]
> pInterface = id <$ eats "=" <*>
>   many (id <$ many (eats "=") <*> col <* eats "|")
>   <* many (eats "=") <* spcu <* eol

> data Type x
>   = V x | B | T [Type x] | [Type x] :-> [(Int, Type x)]
>   deriving Show

> instance Monad Type where
>   return = V
>   V x >>= f = f x
>   B >>= f = B
>   T ts >>= f = T (map (>>= f) ts)
>   (is :-> dos) >>= f = map (>>= f) is :-> map (\ (d, o) -> (d, o >>= f)) dos

> instance Traversable Type where
>   traverse f (V x) = V <$> f x
>   traverse f B = pure B
>   traverse f (T ts) = T <$> traverse (traverse f) ts
>   traverse f (ss :-> its) = (:->) <$> traverse (traverse f) ss <*> 
>     traverse (traverse (traverse f)) its
> instance Foldable Type where
>   foldMap = foldMapDefault
> instance Functor Type where
>   fmap = ap . return
> instance Traversable ((,) a) where
>   traverse f (a, b) = (,) a <$> f b
> instance Foldable ((,) a) where
>   foldMap = foldMapDefault

> pType :: CVIP (Type String)
> pType
>   =    B <$ eats "B"
>   <|>  T [B, B, B, B] <$ eats "H"
>   <|>  V <$> pName
>   <|>  T <$ eats "(" <*> many (spcu *> pType) <* spcu <* eats ")"

> pDeclIn :: CVIP (String, [Type String])
> pDeclIn = (,) <$> pName <*> many (spcu *> pType) <* spcu <* eol

> pDType :: CVIP (Latency, Type String)
> pDType = (,) <$> (length <$> many (eats "+")) <*> pType

> pDeclOut :: CVIP [(Latency, Type String)]
> pDeclOut = many (spcu *> pDType) <* spcu <* eol

> pTiles :: CVIP [Extent Tile]
> pTiles = many (spcu *> pTile) <* spcu <* eol

> type Latency = Int

> data Raw = Raw
>   {  iTypes :: [Type String]
>   ,  iInterface :: [Int]
>   ,  interior :: [[Extent Tile]]
>   ,  oInterface :: [Int]
>   ,  oDTypes :: [(Latency, Type String)]
>   }  deriving Show

> cviParse :: [String] -> Either (String, String) [(String, Raw)]
> cviParse [] = Right []
> cviParse (s : ss) | all isSpace s = cviParse ss
> cviParse (s : ss) = case cvip pDeclIn (0, s) of
>   Nothing -> Left ("component declaration", s)
>   Just (fis, _) -> case ss of
>     [] -> Left ("component definition for " ++ fst fis, "")
>     s : ss -> case cvip pInterface (0, s) of
>       Nothing -> Left ("input boundary for " ++ fst fis, s)
>       Just (iI, _) -> do
>         (f, ss) <- cviDefn fis iI [] ss
>         (f :) <$> cviParse ss

> cviDefn :: (String, [Type String]) -> [Int] -> [[Extent Tile]] -> [String] ->
>   Either (String, String) ((String, Raw), [String])
> cviDefn (f, _) iI lz [] = Left ("end of definition for " ++ f, "")
> cviDefn (f, is) iI lz (s@('=':_) : ss) = case cvip pInterface (0, s) of
>   Nothing -> Left ("end of definition for " ++ f, s)
>   Just (oI, _) -> case ss of
>     [] -> Left ("output types for " ++ f, "")
>     s : ss -> case cvip pDeclOut (0, s) of
>       Nothing -> Left ("output types for " ++ f, s)
>       Just (dos, _) -> Right ((f, Raw is iI (reverse lz) oI dos), ss)
> cviDefn fis iI lz (s : ss) = case cvip pTiles (0, s) of
>   Nothing -> Left ("line of components for " ++ fst fis, s)
>   Just (l, _) -> cviDefn fis iI (l : lz) ss
