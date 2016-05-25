-- Nazev: RKA-2-DKA
-- Autor: Ondrej Krpec, xkrpec01, xkrpec01@stud.fit.vutbr.cz
-- Info: Projekt do predmetu FLP na fakulte FIT VUT v Brne, 6.3.2016

import System.Environment
import System.IO
import System.Directory
import Data.List
import qualified Data.Set as Set 

-- Definice vlastnich datovych struktur
data Rule = Rule { state :: String
		 , symbol :: String
		 , nextState :: String
		 } deriving (Eq, Show)

data Fsm = Fsm { states :: [String]
	       , startState :: String
	       , finiteStates :: [String]
	       , rules :: [Rule]
	       , alphabet :: [String]
	       } deriving (Show)

data Qnew = Qnew { simplified :: String
		 , qStates :: [String]
		 } deriving (Eq)


-- Hlavni funkce programu, zpracovava argumenty prikazove radky a dle nich nasledne ridi beh programu
main :: IO ()
main = do
	args <- getArgs
	let parameters = parseArgs args
	content <- (getContent ( getFileName parameters))

	let nka = parseContent (lines content)
	let dka = Fsm { states = []
		      , startState = startState nka
		      , finiteStates = []
		      , rules = []
		      , alphabet = alphabet nka
		      }

	if (isPrint parameters)
	then printFSM nka
	else printFSM $ nubFsm(simulateRepeat (removeETransitions nka) dka [startState nka] [])


-------------------------------------------------------- Funkce na odstraneni epsilon prechodu z KA -------------------------------------------------


-- Funkce ze vstupniho automatu odstrani epsilon pravidla
-- @param Fsm  -> Vstupni automat
-- @return Fsm -> Vstupni automat bez epsilon prechodu
removeETransitions :: Fsm -> Fsm
removeETransitions fsm = Fsm { states = states fsm
			     , startState = startState fsm
			     , finiteStates = nub $ generateFiniteStates (states fsm) fsm
			     , rules = removeERules (states fsm) fsm
			     , alphabet = alphabet fsm
			     }


-- Funkce odstrani z pravidel pravidla, ktera obsahuji epsilon prechody a vygeneruje misto nich zastupna pravidla
-- @param [String] -> Stavy automatu
-- @param Fsm      -> Vstupni konecny automat
-- @return [Rule]  -> Seznam novych pravidel bez epsilon prechodu
removeERules :: [String] -> Fsm -> [Rule]
removeERules [] fsm     = rules fsm
removeERules [x] fsm    = removeERules' x (createESeal fsm [x] []) x fsm
removeERules (x:xs) fsm = removeERules [x] fsm ++ removeERules xs fsm

removeERules' :: String -> [String] -> String -> Fsm -> [Rule]
removeERules' state' [x] org fsm    = if (state' == x)
			              then generateRules state' org (rules fsm)
			              else removeERules' x (createESeal fsm [x] []) org fsm
removeERules' state' (x:xs) org fsm = removeERules' state' [x] org fsm ++ removeERules' state' xs org fsm


-- Funkce na zaklade stavu a puvodniho stavu vygeneruje vsechny nova pravidla
-- @param String  -> Aktualni stav automatu
-- @param String  -> Puvodni stav automatu, pro ktery se generuji pravidla
-- @param [Rule]  -> Seznam puvodnich pravidel automatu
-- @return [Rule] -> Seznam novych pravidel KA
generateRules :: String -> String -> [Rule] -> [Rule]
generateRules state' oState [] = []
generateRules state' oState [x] = if (state x == state' && symbol x /= [])
				then [Rule { state = oState, symbol = (symbol x), nextState = (nextState x) }]
				else []
generateRules state' oState (x:xs) = generateRules state' oState [x] ++ generateRules state' oState xs


-- Funkce generuje nove koncove stavy automatu, pri odstraneni epsilon prechodu
-- @param [String]  -> Seznam vsech stavu automatu
-- @param Fsm       -> Vstupni konecny automat
-- @return [String] -> Seznam novych konecnych stavu automatu
generateFiniteStates :: [String] -> Fsm -> [String]
generateFiniteStates [] fsm     = finiteStates fsm
generateFiniteStates [x] fsm    = if (areElem (createESeal fsm [x] []) (finiteStates fsm))
			          then finiteStates fsm ++ [x]
			          else finiteStates fsm
generateFiniteStates (x:xs) fsm = generateFiniteStates [x] fsm ++ generateFiniteStates xs fsm


-- Funkce vytvori epsilon uzaver nad danym stavem KA
-- @param Fsm       -> Konecny automat s epsilon prechody
-- @param [String]  -> Pocatecni stavy Qi
-- @param [String]  -> Pocatecni stavy Qi+1
-- @return [String] -> Epsilon uzaver pocatecniho stavu Qi
createESeal :: Fsm -> [String] -> [String] -> [String]
createESeal fsm qi qii = if (qi == qii)
			 then qi
			 else createESeal fsm (nub $ qi ++ qii) (nub $ addElements (qi ++ qii) (nextSealStates (qi ++ qii) (rules fsm)))


-- Funkce vytvori nasledujici stavy epsilon uzaveru
-- @param [String]  -> Predchazejici stavy epsilon uzaveru
-- @param [Rule]    -> Seznam pravidel puvodniho KA
-- @return [String] -> Nove stavy epsilon uzaveru
nextSealStates :: [String] -> [Rule] -> [String]
nextSealStates [] _         = []
nextSealStates [x] rules    = isRule x rules
nextSealStates (x:xs) rules = nextSealStates [x] rules ++ nextSealStates xs rules


--------------------------------------------------- Funkce na vytvoreni deterministickeho konecneho automatu ----------------------------------------


-- Funkce simuluje funkci repeat until urcenou k determinizaci konecneho automatu.
-- Popis algoritmu lze najit ve slidech k predmetu IFJ c.4 24/36, vyucovanem na fakulte FIT VUT v Brne.
-- @param Fsm      -> NKA
-- @param Fsm      -> DKA
-- @param [String] -> Seznam stavu q'
-- @param [Qnew]   -> Seznam stavu QNew
-- @return Fsm     -> DKA vytvoreny ze vstupniho NKA
simulateRepeat :: Fsm -> Fsm -> [String] -> [Qnew] -> Fsm
simulateRepeat nka dka q' []     = if (q' == [])
				   then dka
				   else simulateRepeat nka
						       (iterateFsm nka dka (Qnew { simplified = (simplify q'), qStates = q' }))
						       (qStatesHead (createQNew (createNextState'' q' (alphabet dka) (rules nka)) (states dka) []))
						       (createQNew (createNextState'' q' (alphabet dka) (rules nka)) (states dka) [])
simulateRepeat nka dka q' [x]    = simulateRepeat nka
						  (iterateFsm nka dka (Qnew {simplified = (simplify q'), qStates = q' }))
						  (qStatesHead (nub (createQNew (createNextState'' q' (alphabet dka) (rules nka)) (states dka) [x])))
						  (createQNew (createNextState'' q' (alphabet dka) (rules nka)) (states dka) []) 
	
simulateRepeat nka dka q' (x:xs) = simulateRepeat nka
						  (iterateFsm nka dka (Qnew { simplified = (simplify q'), qStates = q' }))
						  (qStatesHead (tail (nub (createQNew (createNextState'' q' (alphabet dka) (rules nka)) (states dka) [x]))))
						  xs
					    

-- Funkce vypocita jednu iteraci novych stavu noveho deterministickeho konecneho automatu
-- @param Fsm    -> NKA
-- @param Fsm    -> DKA
-- @param String -> Novy stav
-- @return Fsm   -> DKA, ke kteremu jsou pridany nove stavy a pravidla
iterateFsm :: Fsm -> Fsm -> Qnew -> Fsm		
iterateFsm nka dka state' = Fsm { states = states dka ++ [simplified state']
			        , startState = startState dka
			        , finiteStates = finiteStates dka ++ [addFiniteState nka state']
			        , rules = rules dka ++ createRules' nka dka (alphabet dka) (qStates state') (qStates state')
			        , alphabet = alphabet dka
			        }


----------------------------------------------------------------------- Utilitni funkce pro KA ------------------------------------------------------


-- Vlastni implementace funkce head, ktera vraci head qStavu z datove struktury Qnew
-- @param [Qnew]    -> Seznam datoveho typu Qnew
-- @return [String] -> Seznam stavu konecneho automatu
qStatesHead :: [Qnew] -> [String]
qStatesHead list = if (list == [])
		   then []
		   else qStates (head list)


-- Funkce do konecneho automatu na vstupu, prida novy stav zadany parametrem
-- @param Fsm    -> Konecny automat
-- @param String -> Stav automatu
-- @return Fsm   -> Konecnt automat s nove pridanym stavem, ktery byl zadan parametrem.
addState :: Fsm -> String -> Fsm
addState fsm state = Fsm { states = [state] ++ states fsm
			 , startState = startState fsm
			 , finiteStates = finiteStates fsm
			 , rules = rules fsm
			 , alphabet = alphabet fsm
			 }


-- Funkce zkontroluje, zda je ve vstupnim automatu v mnozine koncovych stavu pritomen stav predany parametrem. Pokud ano, vrati jej, pokud ne, vrati prazdny seznam.
-- @param Fsm     -> Konecny automat
-- @param Qnew  -> Stav automatu
-- @return String -> Stav automatu nebo prazdny seznam.
addFiniteState :: Fsm -> Qnew -> String
addFiniteState fsm fState = if (addFiniteState' fsm (qStates fState))
			    then simplified fState
			    else []

addFiniteState' :: Fsm -> [String] -> Bool
addFiniteState' fsm [] = False
addFiniteState' fsm [x] = if (isElem x (finiteStates fsm))
			  then True
			  else False
addFiniteState' fsm (x:xs) = if (addFiniteState' fsm [x])
			     then True
			     else (addFiniteState' fsm xs) 


-- Funkce na zaklade aktualniho stavu, symbolu ze vstupni abecedy a mnoziny pravidel vytvori mozne novy stav
-- @param String    -> Aktualni stav KA
-- @param String    -> Symbol abecedy
-- @param [Rule]    -> Seznam pravidel KA
-- @return [String] -> Novy stav KA
createNextState :: String -> String -> [Rule] -> [String]
createNextState state' alfa []     = []
createNextState state' alfa [x]    = if (state' == state x && alfa == symbol x)
				     then [nextState x]
				     else []
createNextState state' alfa (x:xs) = (createNextState state' alfa [x]) ++ (createNextState state' alfa xs) 

createNextState' :: String -> [String] -> [Rule] -> [Qnew]
createNextState' state' [] _         = []
createNextState' state' [x] rules    = [ Qnew { simplified = simplify (createNextState state' x rules)
					      , qStates = createNextState state' x rules
					      }
				       ]
createNextState' state' (x:xs) rules = (createNextState' state' [x] rules) ++ (createNextState' state' xs rules)

createNextState'' :: [String] -> [String] -> [Rule] -> [Qnew]
createNextState'' [] _ _                = []
createNextState'' [x] alphabet rules    = createNextState' x alphabet rules
createNextState'' (x:xs) alphabet rules = createNextState'' [x] alphabet rules ++ createNextState'' xs alphabet rules


-- Funkce na zaklade nove iterace prida do aktualniho Qnew nove stavy
-- @param [Qnew]  -> Q''
-- @param [String]  -> Stavy DKA
-- @param [Qnew]  -> Aktualni Qnew
-- @return [Qnew] -> Qnew obohacene o Qnew vytvorene dalsi iteraci
createQNew :: [Qnew] -> [String] -> [Qnew] -> [Qnew]
createQNew [] _ qNew          = qNew
createQNew [x] states qNew    = if (isElem (simplified x) states)
			        then []
			        else qNew ++ [x]
createQNew (x:xs) states qNew = createQNew [x] states qNew ++ createQNew xs states qNew


-- Funkce vytvori nova pravidla pro dka na zaklade pravidel zadaneho nka a aktualniho stavu
-- @param Fsm      -> NKA
-- @param Fsm      -> DKA
-- @param [String] -> Vstupni abeceda
-- @param String   -> Novy stav
-- @return [Rule]  -> Seznam novych pravidel
createRules :: Fsm -> Fsm -> [String] -> String -> [String] -> [Rule]
createRules nka dka [] q' qAll  = []
createRules nka dka [x] q' qAll = if ((simplify (createNextState q' x (rules nka))) == [])
			          then []
			          else [ Rule { state = simplify qAll
					      , symbol = x
					      , nextState = simplify (createNextState q' x (rules nka))
					      }
				       ]
createRules nka dka (x:xs) q' qAll = createRules nka dka [x] q' qAll ++ createRules nka dka xs q' qAll

createRules' :: Fsm -> Fsm -> [String] -> [String] -> [String] -> [Rule]
createRules' nka dka alphabet [] _        = []
createRules' nka dka alphabet [x] qAll    = createRules nka dka alphabet x qAll
createRules' nka dka alphabet (x:xs) qAll = createRules nka dka alphabet x qAll ++ createRules' nka dka alphabet xs qAll


-- Funkce odstrani duplicity z konecneho automatu
-- @param Fsm  -> Konecny automat s duplicitami
-- @return Fsm -> Konecny automat bez duplicit
nubFsm :: Fsm -> Fsm
nubFsm fsm = Fsm { states       = removeEmptyStrings (nub $ states fsm)
		 , startState   = startState fsm
		 , finiteStates = removeEmptyStrings (nub $ finiteStates fsm)
		 , rules        = nub $ rules fsm
		 , alphabet     = nub $ alphabet fsm
		 }


-- Funkce vrati seznam stavu, do kterych lze dle mnoziny pravidel a aktualni stavu prechazet
-- @param String   -> Aktualni stav
-- @param [Rule]   -> Seznam pravidel KA
-- @param [String] -> Seznam nasledujicich stavu	 
isRule :: String -> [Rule] -> [String]
isRule state' []     = []
isRule state' [x]    = if (state' == state x && [] == symbol x)
		       then [nextState x]
		       else []
isRule state' (x:xs) = if (state' == state x && [] == symbol x)
		       then [(nextState x)] ++ isRule state' xs
		       else isRule state' xs


----------------------------------------------------------------- Zpracovani argumentu --------------------------------------------------------------


-- Funkce parsuje parametry prikazove radky v tomto formatu:
-- 1. True - Nacti vstupni RKA a vytiskni jej na standardni vystup
-- 2. True - Nacti vstupni RKA, preved jej na DKA a vypis jej na standardni vystup.
-- 3. String - Jmeno vstupniho souboru, pokud soubor neni zadan, nacita se RKA ze standardniho vstupu.
parseArgs :: [[Char]] -> (Bool, Bool, [Char])
parseArgs ["-i", "-t", fileName] = error "Parametry nelze kombinovat."
parseArgs ["-t", "-i", fileName] = error "Parametry nelze kombinovat."
parseArgs ["-i", "-t"] 		 = error "Parametry nelze kombinovat."
parseArgs ["-t", "-i"] 		 = error "Parametry nelze kombinovat."
parseArgs ["-i", fileName] 	 = (True, False, fileName)
parseArgs ["-t", fileName] 	 = (False, True, fileName)
parseArgs ["-i"] 		 = (True, False, "")
parseArgs ["-t"] 		 = (False, True, "")
parseArgs [fileName] 		 = error "Chybi nektery z parametru -t | -i."
parseArgs [] 			 = error "Chybi nektery z parametru -t | -i."
parseArgs _ 			 = error "Spatne parametry."	


-- Funkce vrati true, pokud byl zadan parametr -i
isPrint :: (Bool, Bool, [Char]) -> Bool
isPrint (x, _, _) = x


-- Funkce vrati true, pokud byl zadan parametr -t
isConvert :: (Bool, Bool, [Char]) -> Bool
isConvert (_, x, _) = x


-- Funkce vrati false, pokud budeme nacitat ze STDIN
isFilePresent :: [Char] -> Bool
isFilePresent fileName = if length fileName > 0
		  	 then True
		 	 else False


-- Funkce vrati nazev vstupniho souboru. Pokud se ma cist ze STDIN, vrati prazdny retezec
getFileName :: (Bool, Bool, [Char]) -> [Char]
getFileName (_, _, x) = x


-- Funkce vrati obsah souboru, pripadne nacte vstupni data ze STDIN
getContent :: [Char] -> IO String
getContent fileName = if (isFilePresent fileName)
		      then readFile fileName
		      else getContents	
																		   

----------------------------------------------------------- IO Funkce ---------------------------------------------------

-- Funkce ocekavana na vstupu konecny automat, ktery vytiskne ve formatu dle zadani na STDOUT
-- @param Fsm -> Konecny automat
-- @return IO -> IO operace
printFSM :: Fsm -> IO ()
printFSM fsm = do putStrLn (mergeStrings (states fsm))
		  putStrLn (startState fsm)
		  putStrLn (mergeStrings (finiteStates fsm))
		  putStrLn (rulesToString (rules fsm))
		  return ()


-- Funkce parsuje obsah retezce na datovou strukturu Fsm reprezentujici konecny automat. Vyuziva techto pomocnych funkci:
-- 1. parseStates'       -> pro parsovani stavu KA
-- 2. parseStartState'   -> pro parsovani pocatecniho stavu KA
-- 3. parseFiniteStates' -> pro parsovani koncovych stavu KA
-- 4. parseRules'	 -> pro parsovani pravidel KA
-- 5. parseAlphabet'	 -> pro parsovani abecedy
-- @param [String] -> Seznam retezcu
-- @return Fsm     -> Rozparsovany seznam retezcu do podoby konecneho automatu
parseContent :: [String] -> Fsm
parseContent content = if (null content || length content < 4) 
		       then error "Chybny vstupni soubor."
		       else Fsm { states       = parseStates' content
				, startState   = parseStartState' content
				, finiteStates = parseFiniteStates' content
				, rules        = parseRules' content
				, alphabet     = parseAlphabet' (parseRules' content)
				}

parseStates' :: [String] -> [String]
parseStates' ( states : _ ) = splitAtComma states

parseStartState' :: [String] -> String
parseStartState' content = head (tail content)

parseFiniteStates' :: [String] -> [String]
parseFiniteStates' ( _ : _ : states : _ ) = splitAtComma states

parseRules' :: [String] -> [Rule]
parseRules' ( _ : _ : _ : rules ) = parseRules'' rules

parseRules'' :: [String] -> [Rule]
parseRules'' []		  = error "Vstupni automat neobsahuje zadna pravidla."
parseRules'' [rule] 	  = [parseRule' (splitAtComma rule)]
parseRules'' (rule:rules) = ([parseRule' (splitAtComma rule)]) ++ (parseRules'' rules)

parseRule' :: [String] -> Rule
parseRule' (state : symbol : nextState : err) = if null err
						then Rule { state = state
							  , symbol = symbol
							  , nextState = nextState
							  }
						else error "Chybne zadana pravidla."

parseAlphabet' :: [Rule] -> [String]
parseAlphabet' []     = error "Vstupni automat neobsahuje zadna pravidla."
parseAlphabet' [x]    = [symbol x]
parseAlphabet' (x:xs) = removeEmptyStrings (nub $ [symbol x] ++ parseAlphabet' xs)


-- Funkce rozdeli retezec do seznamu podle delimiteru ','
-- @param String    -> Vstupni retezec
-- @return [String] -> Vstupni retezec rozdeleny do seznamu podle delimiteru ','
splitAtComma :: String -> [String]
splitAtComma ""  = []
splitAtComma seq = let (s, seq') = break (== ',') seq
		   in s : case seq' of
			       []	   -> []
			       (_ : seq'') -> splitAtComma seq''


--------------------------------------------------------------------- Utility -----------------------------------------------------------------------


-- Funkce prida do seznamu vsechny prvky z druheho seznamu, ktere v prvnim chybi
-- @param [String]  -> Seznam prvku, do ktereho se budou pridavat prvky
-- @param [String]  -> Seznam prvku, ktere se budou pridavat do prvniho seznamu
-- @return [String] -> Novy Seznam
addElements :: [String] -> [String] -> [String]
addElements list []     = list 
addElements list [x]    = if (x `elem` list )
			    then list 
			    else list ++ [x]
addElements list (x:xs) = addElements list [x] ++ addElements list xs


-- Funkce spoji seznam do jedineho retezce bez delimiteru
-- @param [String] -> Seznam retezcu
-- @return String  -> Jediny retezec
simplify :: [String] -> String
simplify []     = []
simplify [x]    = x
simplify (x:xs) = x ++ simplify xs


-- Spoji retezce ze seznamu do jednoho retezce. Jednotlive polozky seznamu jsou oddeleny carkou
-- @param [String] -> Seznam retezcu
-- @return String  -> Spoji seznam retezcu do jedineho retezce. Jednotlive polozky seznamu jsou od sebe oddeleny carkou.
mergeStrings :: [String] -> String
mergeStrings []     = ""
mergeStrings [x]    = x
mergeStrings (x:xs) = x ++ [','] ++ (mergeStrings xs) 


-- Funkce odstrani prazdne retezce ze seznamu stringu
-- @param [String]  -> Seznam retezcu
-- @return [String] -> Seznam retezcu bez prazdnych prvku
removeEmptyStrings :: [String] -> [String]
removeEmptyStrings list = [x | x <- list, x /= ""]


-- Funkce spoji seznam pravidel do jednoho retezce, jednotliva pravidla jsou oddeleny '\n'
-- @param [Rule]  -> Seznam pravidel konecneho automatu
-- @return String -> Pravidla konecneho automatu ulozene jako retezec. Symbol abecedy je od stavu automatu oddelen carkou.
--                   Jednotlive pravidla automatu jsou od sebe oddeleny symbolem konce radku.
rulesToString :: [Rule] -> String
rulesToString []     = ""
rulesToString [x]    = ruleToString x
rulesToString (x:xs) = ruleToString x ++ ['\n'] ++ rulesToString xs


-- Funkce spoji pravidlo KA do jednoho retezce
-- @param Rule    -> Pravidlo konecneho automatu
-- @return String -> Pravidlo konecneho automatu ulozene jako retezec. Symbol abecedy je od stavu automatu oddelen carkou.
ruleToString :: Rule -> String
ruleToString rule = state rule ++ [','] ++ symbol rule ++ [','] ++ nextState rule


-- Funkce vraci true v pripade, ze prvek je elementem seznamu
-- @param String   -> Prvek, ktery bude otestovan
-- @param [String] -> Seznam, ve kterem se bude hledat zadany prvek
-- @return Bool	   -> Vraci uspesnost vyhledani prvku v seznamu
isElem :: String -> [String] -> Bool
isElem item list = if item `elem` list
		   then True
		   else False

-- Funkce vraci true v pripade, ze vsechny prvky prvniho seznamu jsou elementy druheho seznamu
-- @param [String] -> Seznam prvku, ktere budou testovany
-- @param [String] -> Seznam prvku, vuci kteremu se bude testovat
-- @return Bool    -> Vraci uspesnost vyhledani prvku v seznamu
areElem :: [String] -> [String] -> Bool
areElem [] _        = False
areElem [x] list    = if (x `elem` list)
		      then True
		      else False
areElem (x:xs) list = if (x `elem` list)
		      then True
		      else areElem xs list

-- Funkce odstrani z druheho seznamu vsechny prvky, ktere se nachazi v prvnim seznamu
-- @param [String] -> Seznam prvku, ktere budou odstraneny z druheho seznamu
-- @param [String] -> Seznam prvku, ve kterych bude cisteno :-)
-- @return [String] -> Vrati druhy seznam bez prvku, ktere byly v prvnim seznamu
removeElem :: [String] -> [String] -> [String]
removeElem _ []          = []
removeElem [] xs         = xs
removeElem [x] [y]       = if (x == y)
		           then []
		           else [y]
removeElem [x] (y:ys)    = removeElem [x] [y] ++ removeElem [x] ys
removeElem (x:xs) [y]    = removeElem [x] [y] ++ removeElem xs [y]
removeElem (x:xs) (y:ys) = removeElem [x] [y] ++ removeElem xs ys


