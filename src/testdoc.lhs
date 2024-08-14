We begin with a tiny programming language for arithmetic expressions and if-then-else. 
We define a datatype `Expr` of expressions in one variable.
\begin{code}
data Expr = Var | Constt Double | Add Expr Expr | Mult Expr Expr
          | IfLess Double Expr Expr
\end{code}
<details class="code-details">
<summary>(Pretty printing routines)</summary>
\begin{code}
instance Show Expr where
  show Var = "x"
  show (Constt r)  = show $ (fromInteger $ round $ r * 10) / 10.0
  show (Add e1 e2) = "(" ++ show e1 ++ " + "++show e2++")"
  show (Mult e1 e2) = "(" ++ show e1 ++ " . "++show e2++")"
  show (IfLess r e1 e2) =
    "(if x<" ++ show (Constt r) ++ " then "++show e1 ++" else "++show e2++")"
\end{code}

</details>
<br>
We define a standard evaluation function, essentially a definitional interpreter. 

\begin{code}
eval :: Expr -> Double -> Double
eval Var x = x
eval (Constt r) _ = r
eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)
eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)
eval (IfLess r e1 e2) x = if x < r then eval e1 x else eval e2 x
\end{code}