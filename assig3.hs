import System.Environment
import System.IO (stdout,stderr,hPutStr,hPutStrLn)
import Data.Char
import Data.List
import Data.Bits

-- Data type for mathematical expressions

data ME = Num Int 
        | Var Char
        | Add ME ME
        | Sub ME ME
        | Mul ME ME
        | Power ME Int
        | Neg ME
        | Group ME
        deriving (Show, Ord, Eq)

-- 1. Symbolic derivative function

deriv :: ME -> Char -> ME

deriv (Num _) x = Num 0
deriv (Var x) y
   | x == y    = Num 1
   | otherwise = Num 0
deriv (Add f g) x = Add (deriv f x) (deriv g x)
deriv (Sub f g) x = Sub (deriv f x) (deriv g x)
deriv (Mul f g) x = Add (Mul g (deriv f x)) (Mul f (deriv g x))
deriv (Power f n) x 
   | n == 0    = Num 0
   | otherwise = Mul (Mul (Num n) (Power f (n - 1))) (deriv f x)
deriv (Neg f) x = Neg (deriv f x)
deriv (Group f) x = deriv f x

-- 2. Inside-out expression simplifier

makeNum :: Int -> ME
makeVar :: Char -> ME
makeAdd :: ME -> ME -> ME
makeSub :: ME -> ME -> ME
makeMul :: ME -> ME -> ME
makePower :: ME -> Int -> ME
makeNeg :: ME -> ME
makeGroup :: ME -> ME

simplifyME :: ME -> ME

simplifyME (Num n) = makeNum n
simplifyME (Var x) = makeVar x
simplifyME (Add f g) = makeAdd (simplifyME f) (simplifyME g)
simplifyME (Sub f g) = makeSub (simplifyME f) (simplifyME g)
simplifyME (Mul f g) = makeMul (simplifyME f) (simplifyME g)
simplifyME (Power f n) = makePower (simplifyME f) n
simplifyME (Neg f) = makeNeg (simplifyME f)
simplifyME (Group f) = makeGroup (simplifyME f)


makeNum n = Num n

makeVar x = Var x

-- f + 0 = f 
makeAdd f (Num 0) = f
-- m + n = k 
makeAdd (Num m) (Num n) = Num (m + n)
-- n + f = f + n 
makeAdd (Num n) f = makeAdd f (Num n)
-- f + m + n = f + k 
makeAdd (Add f (Num m)) (Num n) = makeAdd f (Num (m + n))
-- f + n + g = f + g + n 
makeAdd (Add f (Num n)) g = makeAdd f (makeAdd g (Num n))
-- m * f + n * f = k * f 
makeAdd (Mul (Num m) f) (Mul (Num n) g)
   | f == g    = Mul (Num (m + n)) f
   | otherwise = Add (Mul (Num m) f) (Mul (Num n) g)
-- Default add
makeAdd f g = Add f g

-- 0 - f = -f 
makeSub (Num 0) f = makeNeg f
-- f - 0 = f 
makeSub f (Num 0) = f
-- m - n = k 
makeSub (Num m) (Num n) = Num (m - n)
-- m - f = -f + m 
makeSub (Num m) f = makeAdd (Neg f) (Num m)
-- f - m - n = f - k 
makeSub (Sub f (Num m)) (Num n) = makeSub f (Num (m + n))
-- Default sub
makeSub f g = Sub f g

-- 0 * f = 0 
makeMul (Num 0) f = Num 0
-- 1 * f = f 
makeMul (Num 1) f = f
-- m * n = k 
makeMul (Num m) (Num n) = Num (m * n)
-- f * n = n * f 
makeMul f (Num n) = makeMul (Num n) f
-- f * (g * h) = f * g * h
makeMul f (Mul g h) = makeMul (makeMul f g) h
-- f ^ m * f ^ n = f ^ k
makeMul (Power f m) (Power g n)
   | f == g    = Power f (m + n)
   | otherwise = Mul (Power f m) (Power g n)
-- f ^ m * g = g * f ^ m
makeMul (Power f m) g = makeMul g (Power f m)
-- Default mul
makeMul f g = Mul f g

-- f ^ 0 = 1 
makePower f 0 = Num 1
-- f ^ 1 = f 
makePower f 1 = f
-- m ^ n = k 
makePower (Num m) n = Num (m ^ n)
-- Default power
makePower f n = Power f n

-- Used to cancel double negatives instead of stacking them
makeNeg (Neg f) = f
-- Eliminates the case of negative zero
makeNeg (Num 0) = (Num 0)
makeNeg f = Neg f

makeGroup f = Group f

-- 3. Unparser for algebraic expressions

unparseME :: ME -> [Char]

unparseME (Num n) = show n
unparseME (Var x) = [x]
unparseME (Add f g) = unparseME f ++ "+" ++ unparseME (groupTerms g)
unparseME (Sub f g) = unparseME f ++ "-" ++ unparseME (groupTerms g)
unparseME (Mul f g) = unparseME (groupTerms f) ++ "*" ++ unparseME (groupFactors g)
unparseME (Power f n) = unparseME (groupElements f) ++ "**" ++ show n
unparseME (Neg x) = "-" ++ unparseME (groupTerms x)
unparseME (Group f) = "(" ++ unparseME f ++ ")"

groupTerms (Add f g) = Group (Add f g)
groupTerms (Sub f g) = Group (Sub f g)
groupTerms (Neg x) = Group (Neg x)
groupTerms x = x
groupFactors (Mul f g) = Group (Mul f g)
groupFactors x = groupTerms x
groupElements (Power f n) = Group (Power f n)
groupElements x = groupFactors x

-- 4. Parser for algebraic expressions

parseME :: [Char] -> Maybe (ME, [Char])
parseSignedTerm :: [Char] -> Maybe (ME, [Char])
parseTerm :: [Char] -> Maybe (ME, [Char])
parseFactor :: [Char] -> Maybe (ME, [Char])
parseElement :: [Char] -> Maybe (ME, [Char])
parseVariable :: [Char] -> Maybe (ME, [Char])
parseNumeral :: [Char] -> Maybe (ME, [Char])

parseNumeral "" = Nothing
parseNumeral (c:s) 
  | isDigit c = extendNumeral ((digitToInt c), s)
  | otherwise = Nothing

-- Used to read an entire number and combine the digits
extendNumeral :: (Int, [Char]) -> Maybe (ME, [Char])

extendNumeral (digits, "") = Just ((Num digits), "")
extendNumeral (digits, (c:s))
  | isDigit c = extendNumeral (((10 * digits) + (digitToInt c)), s)
  | otherwise = Just ((Num digits), c:s)

parseVariable "" = Nothing
parseVariable (c:s)
   | isLetter c && isLower c = Just ((Var c), s)
   | otherwise               = Nothing

parseElement ('(':more) =
    case parseME(more) of
        Just (me, ')':yet_more) -> Just (Group me, yet_more)
        _ -> Nothing
parseElement s
   | isLetter (s!!0) = parseVariable s
   | otherwise       = parseNumeral s

parseFactor s =
    case parseElement(s) of
        Just (r, more_chars) -> extendFactor(r, more_chars)
        _ -> Nothing

extendFactor :: (ME, [Char]) -> Maybe (ME, [Char])

extendFactor (e1, []) = Just (e1, [])
extendFactor (e1, '*' : '*' : power) =
    case parseNumeral(power) of 
        Just(e2, more) -> extendFactor(Power e1 (read (unparseME e2)), more)
        _ -> Nothing
extendFactor(e1, c:more) = Just (e1, c:more)

parseTerm s =
    case parseFactor(s) of
        Just (r, more_chars) -> extendTerm(r, more_chars)
        _ -> Nothing

extendTerm :: (ME, [Char]) -> Maybe (ME, [Char])

extendTerm (e1, []) = Just (e1, [])
extendTerm (e1, '*' : constant) =
    case parseTerm(constant) of 
        Just(e2, more) -> extendTerm(Mul e1 e2, more)
        _ -> Nothing
extendTerm(e1, c:more) = Just (e1, c:more)

parseSignedTerm ('-':s) =
   case parseTerm(s) of
       Just (me, more) -> Just (Neg me, more)
       _ -> Nothing
parseSignedTerm s = parseTerm s

parseME s =
    case parseSignedTerm(s) of
        Just (r, more_chars) -> extendME(r, more_chars)
        _ -> parseSignedTerm s

extendME :: (ME, [Char]) -> Maybe (ME, [Char])

extendME (e1, []) = Just (e1, [])
extendME (e1, '-' : difference) =
    case parseTerm(difference) of 
        Just(e2, more) -> extendME(Sub e1 e2, more)
        _ -> Nothing
extendME (e1, '+' : sum) =
    case parseTerm(sum) of 
        Just(e2, more) -> extendME(Add e1 e2, more)
        _ -> Nothing
extendME(e1, c:more) = Just (e1, c:more)

parseMain :: [Char] -> Maybe ME

parseMain s =
    case parseME s of 
        Just (e, []) -> Just e
        _ -> Nothing

-- Command Line interface

findAnswer :: [Char] -> [Char] -> [Char]
findAnswer var me = case parseMain me of
                    Just r -> (unparseME(simplifyME(deriv r (var!!0))))
                    _ -> []

main = do
    [variable, expression] <- getArgs
    hPutStr stdout (findAnswer variable expression)