#lang pyret/check

#Autor: Julio de la Cruz (con ayuda de varias personas como Edwin, Alejandro)
#Descripcion:    Este file basicamente tiene un lenguage de programacion, casi completo. Contiene un interpretador y un parse. Ademas
#                contiene funciones adicionales que ayudan en el proceso de llevar a cabos ciertas operaciones                                                                                                                     
                                                                             

#lang pyret/check

# cfwae.arr - Template of a simple interpreter for CFWAE
# Copyright (C) 2014 - Humberto Ortiz-Zuazaga <humberto.ortiz@upr.edu>

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.


# Bindings map identifiers to expressions
data Binding:
  | bind (name :: String, expr :: CFWAE)
end

# An Environment is a List<Env>
data Env:
  | env (name :: String, value :: CFWAE-Value)
end

# An Environment is a List<Binding>
mt-env = []
xtnd-env = link

# Data type for expressions
                          
data CFWAE:
  | numC (n :: Number)
  | binopC (op :: String, l :: CFWAE, r :: CFWAE)
  | withC (bindings :: List<Binding>, expr :: CFWAE)
  | idC (name :: String)
  | if0C (test-expr :: CFWAE, then-expr :: CFWAE, else-expr :: CFWAE)
  | fdC (args :: List<String>, body :: CFWAE)
  | appC (f :: CFWAE, args :: List<CFWAE>)
end

# and values
data CFWAE-Value:
  | numV (n :: Number)
  | closV (f :: CFWAE, e :: List<Env>) # ExprC must be an fdC
end

#palabras reservadas
keywords = ['+','-','*','/','with','if0','fun']


#Funciones que me ayudaran en el binopC... Estas me permitiran realizar operaciones aritmeticas                                                                                            
fun plus-v(v1, v2): numV(v1.n + v2.n) end
fun mult-v(v1, v2): numV(v1.n * v2.n) end
fun subs-v(v1, v2): numV(v1.n - v2.n) end
fun div-v(v1, v2): if v2 == numV(0):
                      raise("binopC(div-v): You cannot divide by 0")
                   else:
                      numV(v1.n - v2.n) 
                   end
end

fun binop(op :: String, l::CFWAE-Value, r::CFWAE-Value):
doc: "binop recibe dos argumentos y de acuerdo al op hace la operacion necesaria"
                         if op == "+":
                            plus-v(l,r)
                         else if op == "-":
                            subs-v(l,r)
                         else if op == "*":
                            mult-v(l,r)
                         else if op == "/":
                            div-v(l,r)
                         else:
                            raise("binopC: op, not a valid operator")
                         end

end

fun lookup(s :: String, nv :: List<Env>) -> CFWAE-Value:
doc: "lookup recibira un string que sera buscado en la lista de env y si esta devolvera su valor"
  cases (List<Env>) nv:
    | empty => raise("Unbound identifier")
    | link(first, rest) => if first.name == s:
                                 first.value
                           else:
                                 lookup(s, rest)
                           end
  end
where:
lookup("y", [env("y", numV(4))]) is numV(4)
lookup("x", [env("x",numV(2))]) is numV(2)
lookup("y", []) raises("Unbound")
end

fun miWith(mv :: List, kw :: List<String>) -> List<Binding>:
doc: "miWith recibira una lista y una lista de strings... y devolvera una lista de binding"
   cases (List) mv:
     | empty => empty
     | link(f,r) => 
                    if kw.member(list.index(f,0)):
                      raise("miWith. The identifier is in the List")
                    else:
                      link(bind(list.index(f,0), parse(list.index(f,1))), miWith(r,link(list.index(f,0),kw)))
                    end
   end
end

fun withEnv(lbind :: List<Binding>, oldenv :: List<Env>) -> List<Env>:
   doc: "Crea el env que usara el withC"
   cases (List) lbind:
     | empty => empty
     | link(f, r) =>  madeenv = link(env(f.name, interpreter(f.expr, oldenv)), oldenv)
                      link(madeenv, withEnv(r, madeenv))
   end
end

fun parse-list(pl :: List) -> List<CFWAE>:
doc: "Esta funcion recibe una lista de numeros normales (8,9,0, etc) y te devuelve esa lista ya parseada"
     cases(List) pl:
       | empty => empty
       | link(f,r) => link(parse(f), parse-list(r))   
     end
end

fun parse-formals(args :: List<String>, kwords :: List<String>) -> List<String>:
doc: "Esta funcion recibe dos listas de string, una de keywords con la verificara si hay algun elemento de la otra
      lista de strings, si no es asi entonces devolvera la lista de string valida"
     cases (List) args:
       | empty => empty
       | link(f,r) => if kwords.member(f):
                              raise("parse-formals. The identifier is in the List")
                      else:
                              link(f, parse-formals(r,link(f,kwords)))
                      end

     end
end

fun makingMyEnv(formales :: List <String>, reales :: List<CFWAE>, oldenv :: List<Env>) -> List<Env>:
doc: "Esta funcion recibe unos identificadores y unos valores y los guarda en el environment que recibe
      respectivamente bindiados"
 cases(List) formales:
  | empty => oldenv
  | link(first-form, rest-form) => 
     cases(List) reales:
      | empty => raise("makingMyEnv: No hay argumentos reales suficientes")
      | link(first-real, rest-real) => 
           newenv = makingMyEnv(rest-form, rest-real, oldenv)
           link(env(first-form, interpreter(first-real, oldenv)), newenv)
     end
 end
end

#(s == "+") or (s == "-") or (s == "/") or (s == "*") or (s == "if0") or (s == "with") or (s == "fun"):                                                                                                       
fun parse(s) -> CFWAE:
  doc: "Parse reads an s-expression S and returns the abstract syntax tree."
  if Number(s):
    numC(s)
  else if String(s):
      if keywords.member(s):
         raise("reserved names cannot be used as identifiers")
      else:
         idC(s)
      end
  else if List(s):
    cases (List) s:
      | empty => raise("parse: unexpected empty list")
      | link(op, args) =>
         if (op == "+") or (op == "-") or (op == "*") or (op == "/"):
            if args.length() == 2:
                argL = list.index(args, 0)
                argR = list.index(args, 1)
                binopC(op, parse(argL), parse(argR))
            else:
                raise("binopC: need 2 args to operate")
            end
        else if op == "if0": 
            if args.length() == 3:
               mitest = list.index(args, 0)
               mithen = list.index(args, 1) 
               mielse = list.index(args, 2)
               if0C(parse(mitest),parse(mithen),parse(mielse))
            else: 
               raise("if0: need 3 arguments to operate")
            end
        else if op == "with":
            arguments = list.index(args, 0)
            body = list.index(args, 1)
            withC(miWith(arguments, keywords),parse(body))
        else if op == "fun": 
            identifiers = list.index(args,0)
            body = list.index(args,1)
            fdC(parse-formals(identifiers, keywords), parse(body))
        else:
           appC(parse(op), parse-list(args))
        end
    end
  end
where:
  parse(3) is numC(3)
  parse(read-sexpr("(+ 1 2)")) is binopC("+", numC(1), numC(2))
  parse(["with", [["x", 2],["y",4]], ["if0", 1, 1, 2]]) is withC([bind("x", numC(2)), bind("y", numC(4))], if0C(numC(1), numC(1), numC(2)))
  parse(["with", [["x", 2],["y",4]], ["-", 23, 25]]) is
    withC([bind("x", numC(2)), bind("y", numC(4))], binopC("-", numC(23), numC(25)))
  parse(["with", [["x", 2],["x",4]], ["-", 23, 25]]) raises("m")
  parse(read-sexpr("(fun (x x) x)")) raises("T")
  parse(read-sexpr("(fun (x) x)")) is fdC(["x"], idC("x"))
  parse(read-sexpr("((fun (x y) (+ x y)) 3 4)")) is appC(fdC(["x", "y"], binopC("+", idC("x"), idC("y"))), [numC(3), numC(4)])
  parse(read-sexpr("((fun (x) (+ x x)) 2)")) is appC(fdC(["x"], binopC("+", idC("x"), idC("x"))), [numC(2)])
  parse(read-sexpr(("((fun (self n) (self self n)) (fun (self n) (if0 n 0 (+ n (self self (- n 1))))) 10)"))) is 
    appC(fdC(["self", "n"], appC(idC("self"), [idC("self"), idC("n")])), [fdC(["self", "n"], if0C(idC("n"), numC(0), 
    binopC("+", idC("n"), appC(idC("self"), [idC("self"), binopC("-", idC("n"), numC(1))])))), numC(10)])
end


fun interp(w :: CFWAE) -> CFWAE-Value :
doc: "este interpretador me crea un nuevo environment para usarlo en el otro interpretador"
   envi = []
   interpreter(w, envi) #llamando al otro interpretador que recibe environment
end

fun interpreter(e :: CFWAE, mv :: List<Env>) -> CFWAE-Value:
  doc: "Execute the expression E, return the result of evaluation."
  cases (CFWAE) e:
    | numC(n) => numV(n)
    | binopC(op, l, r) => binop(op, interpreter(l,mv), interpreter(r,mv))
    | if0C(i, th, els) => res = interpreter(i, mv)
                          if res == numV(0):
                               interpreter(th, mv)
                          else: 
                               interpreter(els, mv)
                          end
    | withC(binds, expression) =>
        n-env = for map(b from binds):
                   env(b.name, interpreter(b.expr, mv))
                end
        interpreter(expression, n-env.append(mv))
    | idC(name) => lookup(name, mv)
    | fdC(_,_) => closV(e,mv)
    | appC(func, realArgs) => miclos = interpreter(func, mv)
                   nenv = makingMyEnv(miclos.f.args, realArgs, mv)
                   interpreter(miclos.f.body, nenv)
  end
where:
  mv = []
  interpreter(if0C(numC(0), numC(1), numC(2)), mv) is numV(1)
  interpreter(if0C(numC(1), numC(3), numC(2)), mv) is numV(2)
  interpreter(numC(1), mv) is numV(1)
  interpreter(binopC("+", numC(1), numC(3)), mv) is numV(4)
  interpreter(binopC("*", numC(1), numC(3)), mv) is numV(3)
  interpreter(binopC("-", numC(1), numC(3)), mv) is numV(-2)
  interpreter(binopC("/", numC(1), numC(0)), mv) raises("binopC(div-v): You cannot divide by 0")
  interpreter(binopC("/", numC(4), numC(2)), mv) is numV(2)
  interpreter(withC([bind("x", numC(2)), bind("y", numC(4))], binopC("-", idC("x"), idC("y"))), mv) is numV(-2)
  interpreter(appC(fdC(["x"], binopC("+", idC("x"), idC("x"))), [numC(2)]), mv) is numV(4)
  interpreter(appC(fdC(["x", "y"], binopC("+", idC("x"), idC("y"))), [numC(3), numC(4)]), mv) is numV(7)
end

check:
  envi = []
  fun run(s): interpreter(parse(read-sexpr(s)), envi) end
  run("5") is numV(5)
  run("(if0 0 1 2)") is numV(1)
  run("(if0 1 2 3)") is numV(3)
  run("(with ((x 2))
              (+ x 2))") is numV(4)
  run("(with ((x 2) (x 3))
              (+ y x))") raises("m")
  run("((fun (x) (+ x x)) 2)") is numV(4)
  run("(with ((x 2) (y 3))(with((z(+ x y)))(+ x z)))") is numV(7)
  run("((fun (self n) (self self n)) (fun (self n) (if0 n 0 (+ n (self self (- n 1))))) 10)") is numV(55)
  run("((fun (self n) (self self n)) (fun (self n) (if0 n 1 (* n (self self (- n 1))))) 5)") is numV(120)
end
