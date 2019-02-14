-- Nombre : Carlos Montoto Jáuregui

type Var = String
data FProp = V Var | No FProp | Y FProp FProp | O FProp FProp | Si FProp FProp | Sii FProp FProp

f1 = Si (No (V "p")) (Si (V "p") (Y (V "q") (No (V "q"))))
f2 = Y (V "p") (Si (No (V "q")) (No (V "p")))
f3 = Y (V "p")(Y (V "q") (O (No (V "q")) (V "r")))
f4 = Sii (O (V "p") (No (V "q"))) (Y (V "p") (Y (V "q") (O (No (V "p")) (No (V "q")))))
f5 = Si (Sii (V "p") (V "q")) (O (No (V "q")) (No (V "p")))
f6 = O (V "p") (Si (V "p") (V "q"))
f7 = Sii (f1) (f6)

-- FUNCIONES AUXILIARES--
-- No repeticiones --
-- Crea una nueva lista en la que no hay elementos repetidos
noRep :: Eq (a) => [a] -> [a]
noRep [] = []
noRep (x:xs) = x : noRep [y | y <- xs, x /= y]
---------------------
-- asigna valor --
-- Devuelve el valor Bool determinado de la variable v
asigna :: Var -> [(Var, Bool)] -> Bool
asigna a xs = [b | (v, b) <- xs, v == a] !! 0
---------------------
-- realiza funcion --
-- Realiza la tabla de verdad de FProp para saber si es o no tautologia
rFuncion :: FProp -> [(Var, Bool)] -> Bool
rFuncion (V a) xs = asigna a xs
rFuncion (No a) xs = not (rFuncion a xs)
rFuncion (Y a b) xs = (rFuncion a xs) && (rFuncion b xs)
rFuncion (O a b) xs = (rFuncion a xs) || (rFuncion b xs)
rFuncion (Si a b) xs = (\ x y z-> if ((rFuncion x z) == True) && ((rFuncion y z) == False) then False else True) a b xs
rFuncion (Sii a b) xs = (\ x y z-> if ((rFuncion x z) == True) && ((rFuncion y z) == True) then True else False) a b xs
---------------------
-- iniciaBool --
-- Genera los posibles valores de las variables
-- Función consultada en:
-- https://github.com/1ambda/haskell/blob/master/FP101/week5/tautology.hs
iniciaBool :: Int -> [[Bool]]
iniciaBool 0 = [[]]
iniciaBool n = map (False:) (iniciaBool (n-1)) ++ map (True:) (iniciaBool (n-1))
---------------------
-- creaLista --
-- Crea la lista de tuplas con los valores Bool de la variables
creaLista :: [Var] -> [[(Var, Bool)]]
creaLista xs = map (zip xs) (iniciaBool (length xs))
--------------------------
-- consecuencias_aux --
-- Genera una lista de FProp con los FProp que son consecuencia uno de otro
consecuencias_aux :: FProp -> [FProp] -> [FProp]
consecuencias_aux _ [] = []
consecuencias_aux f (x:xs) = (\a b c -> if (consecuencia b a) then b : (consecuencias_aux a c) else (consecuencias_aux a c)) f x xs
---------------------------
-- fPropString -- 
-- Genera el String del FProp para mostrarlo
-- Nota: He utilizado " ^ " para Y y " V " para O porque no me permitia utilizar \ para " /\ " y para " \/ "
fPropString :: FProp -> String
fPropString (V a) =  a
fPropString (No a) = "~" ++ fPropString a
fPropString (Y a b) = "(" ++ fPropString a ++ " ^ " ++ fPropString b ++ ")"
fPropString (O a b) = "(" ++ (fPropString a) ++ " V " ++ (fPropString b) ++ ")"
fPropString (Si a b) = "(" ++ (fPropString a) ++ " -> " ++ (fPropString b) ++ ")"
fPropString (Sii a b) = "(" ++ (fPropString a) ++ " <-> " ++ (fPropString b) ++ ")"
---------------------------
-- igualdad --
-- Comprueba que dos FProp sean iguales como especifica el enunciado
igualdad :: FProp -> FProp -> Bool
igualdad (V a) (V b) = a == b
--
igualdad (No a) (No b) = igualdad a b
--
igualdad (Y a b) (Y c d) = (igualdad a c) && (igualdad b d) || (igualdad a d) && (igualdad b c)
--
igualdad (O a b) (O c d) = (igualdad a c) && (igualdad b d) || (igualdad a d) && (igualdad b c)
--
igualdad (Si a b) (Si c d) = (igualdad a c) && (igualdad b d) || (igualdad a d) && (igualdad b c)
--
igualdad (Sii a b) (Sii c d) = (igualdad a c) && (igualdad b d) || (igualdad a d) && (igualdad b c)
--
igualdad _ _ = False
---------------------------
-- Equivalentes_aux --
-- Crea una lista con los FProp que son equivalentes a f
equivalentes_aux :: FProp -> [FProp] -> [FProp]
equivalentes_aux f [] = []
equivalentes_aux f1 (f:fs) = (\x y z -> if (equivalente x y) then y: equivalentes_aux x (filter (/= y) z) else equivalentes_aux x z) f1 f fs 
---------------------------
---------------------------

-- FUNCIONES PEDIDAS -- 
-- vars f --
vars :: FProp -> [Var]
vars (V a) = [a]
vars (No a) = noRep (vars a)
vars (Y a b) = noRep (vars a ++ vars b)
vars (O a b) = noRep (vars a ++ vars b)
vars (Si a b) = noRep (vars a ++ vars b)
vars (Sii a b) = noRep (vars a ++ vars b)
-----------------------

-- tautologia --
tautologia :: FProp -> Bool
tautologia f = and [rFuncion f lista | lista <- creaLista (vars f)]
------------------

-- satisfactible --
satisfactible :: FProp -> Bool
satisfactible f = or [rFuncion f lista | lista <- creaLista (vars f)]
---------------------

-- consecuencia --
consecuencia :: FProp -> FProp -> Bool
consecuencia f1 f2 = (\x y -> if (x == True) && (y == True) then True else False) (tautologia f2) (tautologia f1)
---------------------

-- equivalente --
-- Nota: Supongo que en el enunciado de la practica hay un error (ya que en ella la funcion equivalente hace lo mismo que la funcion consecuencia)
-- y defino la funcion equivalente como que dos funciones (f1 y f2) son equivalentes si al ser una True la otra tambien lo es o si al ser la primera False
-- la segunda tambien lo es.
equivalente :: FProp -> FProp -> Bool
equivalente f1 f2 = (\x y -> if x == y then True else False) (tautologia f2) (tautologia f1)

---------------------

-- consecuencias --
consecuencias :: [FProp] -> [(FProp, [FProp])]
consecuencias fs = [(f, consecuencias_aux f fs)| f <- fs]
----------------------

-- equivalentes -- 
equivalentes :: [FProp] -> [[FProp]]
equivalentes xs = [noRep (f : equivalentes_aux f xs) | f <- xs]
------------------
------------------

-- INSTANCIAS --
-- instancia de Eq --
instance Eq FProp where
 f1 == f2 = igualdad f1 f2
---------------------

-- instancia de Ord --
instance Ord FProp where
 f1 <= f2 = consecuencia f1 f2
----------------------

-- instancia de Show --
instance Show FProp where
 show f = fPropString f
------------------------
------------------------
