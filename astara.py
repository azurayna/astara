from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from typing import Any

import pyparsing as pp

Rule = str
Expr = str | dict[str, Any]


@dataclass
class VarInfo:
    var_type: Expr
    definition: Expr


class Context:
    def __init__(self, bare: bool = False) -> None:
        self.variables: dict[str, VarInfo] = {}
        if not bare:
            self._init_prelude()

    def _init_prelude(self) -> None:
        self.postulate("Nat", "Type")
        self.postulate("zero", "Nat")
        self.postulate("succ", "Nat -> Nat")
        self.postulate(
            "Nat.ind",
            "(motive : Nat -> Type) -> (motive zero)"
            " -> ((k : Nat) -> motive k -> motive (succ k))"
            " -> (n : Nat) -> motive n",
        )

        self.postulate("Id", "(A : Type) -> A -> A -> Type")
        self.postulate("refl", "(A : Type) -> (x : A) -> Id A x x")
        self.postulate(
            "Id.ind",
            "(A : Type) -> (x : A)"
            " -> (motive : (y : A) -> Id A x y -> Type)"
            " -> motive x (refl A x)"
            " -> (y : A) -> (p : Id A x y) -> motive y p", 
        )

    def compute_id(self, fun: Expr, proof: Expr) -> Expr:
        default_output = {"rule": "fun_elim", "fun": fun, "var": proof}

        head, args = self._unwrap_app(fun)
        if head != "Id.ind":
            return default_output
        if len(args) != 5:
            return default_output

        id_type, left, motive, refl_case, right = args
        proof_head, proof_args = self._unwrap_app(proof)
        if proof_head != "refl" or len(proof_args) != 2:
            return default_output

        refl_type, refl_term = proof_args
        if not (self.judge(id_type, refl_type) and self.judge(left, refl_term)):
            return default_output

        if not self.judge(right, left):
            return default_output

        return self.compute(refl_case)

    def define(self, name: str, var_type: Expr, definition: Expr, *, override: bool = False) -> None:
        if not override and name in self.variables:
            raise ValueError(f"Variable '{name}' is already defined.")

        var_type = self.parse(var_type) if isinstance(var_type, str) else var_type
        definition = self.parse(definition) if isinstance(definition, str) else definition

        if not self._is_type_value(self.check(var_type)):
            raise ValueError(f"Declared type of '{name}' is not a type.")

        if definition != "axiom" and not self.judge(self.check(definition), var_type):
            raise ValueError(f"Definition of '{name}' does not match its declared type.")

        self.variables[name] = VarInfo(var_type=var_type, definition=definition)

    def postulate(self, name: str, var_type: Expr, *, override: bool = False) -> None:
        self.define(name, var_type, "axiom", override=override)

    def copy_with_dummy(self, name: str, var_type: Expr) -> "Context":
        new_context = Context(bare=True)
        new_context.variables = self.variables.copy()
        if name != "_":
            new_context.postulate(name, var_type, override=True)
        return new_context

    def fresh_dummy_name(self) -> str:
        candidate = 1
        for name in self.variables:
            if name.startswith("_x"):
                try:
                    candidate = max(candidate, int(name[2:]) + 1)
                except ValueError as exc:
                    raise ValueError(f"Invalid variable name '{name}' in context.") from exc
        return f"_x{candidate}"

    @staticmethod
    @lru_cache(maxsize=1)
    def _parser() -> pp.ParserElement:
        identifier = pp.Word(pp.alphanums + "_" + ".")
        expr = pp.Forward()
        atom = identifier | pp.Suppress("(") + expr + pp.Suppress(")")

        def make_app(tokens: list[Expr]) -> Expr:
            result: Expr = tokens[0]
            for arg in tokens[1:]:
                result = {"rule": "fun_elim", "fun": result, "var": arg}
            return result

        app_expr = pp.Group(atom[1, ...]).setParseAction(
            lambda t: make_app(t[0]) if len(t[0]) > 1 else t[0][0]
        )

        binding = pp.Suppress("(") + identifier + pp.Suppress(":") + expr + pp.Suppress(")")
        binding.setParseAction(lambda t: (t[0], t[1]))

        lambda_param_typed = binding.copy()
        lambda_param_untyped = identifier.copy()
        lambda_single_param = lambda_param_typed | lambda_param_untyped
        lambda_arrow = pp.Literal("=>")

        def make_lambda(tokens: list[Expr]) -> Expr:
            body = tokens[-1]
            for param in reversed(tokens[:-1]):
                if isinstance(param, tuple):
                    var, dom = param
                    body = {"rule": "fun_intro", "dom": dom, "var": var, "body": body}
                else:
                    body = {"rule": "fun_intro", "dom": "_", "var": param, "body": body}
            return body

        lambda_expr = (lambda_single_param[1, ...] + pp.Suppress(lambda_arrow) + expr).setParseAction(
            make_lambda
        )

        term = lambda_expr | binding | app_expr
        arrow = pp.Literal("->")

        def make_arrow(tokens: list[Expr]) -> Expr:
            parts = list(tokens)
            result = parts[-1]
            for part in reversed(parts[:-1]):
                if isinstance(part, tuple):
                    var, dom = part
                    result = {"rule": "fun_form", "dom": dom, "var": var, "cod": result}
                else:
                    result = {"rule": "fun_form", "dom": part, "var": "_", "cod": result}
            return result

        expr <<= (term + pp.ZeroOrMore(pp.Suppress(arrow) + term)).setParseAction(
            lambda t: make_arrow(t) if len(t) > 1 else t[0]
        )

        return expr

    def parse(self, text: str) -> Expr:
        result = self._parser().parseString(text, parseAll=True)
        return result[0]

    def unparse(self, parsed: Expr) -> str:
        def unparse_term(t: Expr) -> str:
            if isinstance(t, str):
                return t
            rule = t.get("rule")

            if rule == "fun_form":
                dom = t["dom"]
                cod = t["cod"]
                dom_s = unparse_term(dom)
                if t["var"] != "_":
                    left = f"({t['var']} : {dom_s})"
                else:
                    if isinstance(dom, dict) and dom.get("rule") in ("fun_form", "fun_intro"):
                        left = f"({dom_s})"
                    else:
                        left = dom_s
                return f"{left} -> {unparse_term(cod)}"

            if rule == "fun_elim":
                fun = t["fun"]
                args = [t["var"]]
                while isinstance(fun, dict) and fun.get("rule") == "fun_elim":
                    args.append(fun["var"])
                    fun = fun["fun"]
                args.reverse()

                fun_s = unparse_term(fun)
                if isinstance(fun, dict) and fun.get("rule") in ("fun_form", "fun_intro"):
                    fun_s = f"({fun_s})"

                parts = [fun_s]
                for a in args:
                    a_s = unparse_term(a)
                    parts.append(f"({a_s})" if isinstance(a, dict) else a_s)
                return " ".join(parts)

            if rule == "fun_intro":
                params = []
                body = t
                while isinstance(body, dict) and body.get("rule") == "fun_intro":
                    params.append((body["var"], body["dom"]))
                    body = body["body"]

                param_strs = []
                for v, d in params:
                    d_s = unparse_term(d)
                    param_strs.append(f"({_fmt_param(v)} : {d_s})")
                return f"{' '.join(param_strs)} => {unparse_term(body)}"

            return str(t)

        def _fmt_param(name: str) -> str:
            return "_" if name == "_" else name

        return unparse_term(parsed)

    def substitute(self, expression: Expr, variable: str, value: Expr) -> Expr:
        if isinstance(expression, str):
            return value if expression == variable else expression

        rule = expression["rule"]
        if rule in ("fun_form", "fun_intro"):
            dom = self.substitute(expression["dom"], variable, value)
            binder = expression["var"]
            if binder == variable:
                return {**expression, "dom": dom}
            if binder in self._free_vars(value):
                fresh = self._fresh_name(
                    self._free_vars(expression[("cod" if rule == "fun_form" else "body")])
                    | self._free_vars(value)
                    | {binder, variable}
                )
                renamed_body = self._rename_free(
                    expression[("cod" if rule == "fun_form" else "body")], binder, fresh
                )
                body_key = "cod" if rule == "fun_form" else "body"
                return {
                    **expression,
                    "dom": dom,
                    "var": fresh,
                    body_key: self.substitute(renamed_body, variable, value),
                }
            body_key = "cod" if rule == "fun_form" else "body"
            body = self.substitute(expression[body_key], variable, value)
            return {**expression, "dom": dom, body_key: body}

        if rule == "fun_elim":
            return {
                "rule": "fun_elim",
                "fun": self.substitute(expression["fun"], variable, value),
                "var": self.substitute(expression["var"], variable, value),
            }

        raise ValueError(f"Unknown expression rule '{rule}' for substitution.")

    def judge(self, expression1: Expr, expression2: Expr) -> bool:
        expr1 = self.compute(self.parse(expression1) if isinstance(expression1, str) else expression1)
        expr2 = self.compute(self.parse(expression2) if isinstance(expression2, str) else expression2)

        if isinstance(expr1, str) and isinstance(expr2, str):
            level1 = self._type_level(expr1)
            level2 = self._type_level(expr2)
            if level1 is not None and level2 is not None:
                return level1 == level2
            return expr1 == expr2

        if self._both_rule(expr1, expr2, "fun_form"):
            if not self.judge(expr1["dom"], expr2["dom"]):
                return False
            name = self.fresh_dummy_name()
            new_context = self.copy_with_dummy(name, expr1["dom"])
            return new_context.judge(
                new_context.substitute(expr1["cod"], expr1["var"], name),
                new_context.substitute(expr2["cod"], expr2["var"], name),
            )

        if self._both_rule(expr1, expr2, "fun_intro"):
            if not self.judge(expr1["dom"], expr2["dom"]):
                return False
            name = self.fresh_dummy_name()
            new_context = self.copy_with_dummy(name, expr1["dom"])
            return new_context.judge(
                new_context.substitute(expr1["body"], expr1["var"], name),
                new_context.substitute(expr2["body"], expr2["var"], name),
            )

        if self._both_rule(expr1, expr2, "fun_elim"):
            return self.judge(expr1["fun"], expr2["fun"]) and self.judge(
                expr1["var"], expr2["var"]
            )

        return False

    def compute_elim_nat(self, fun: Expr, n: Expr) -> Expr:
        default_output = {"rule": "fun_elim", "fun": fun, "var": n}

        if not (isinstance(fun, dict) and fun.get("rule") == "fun_elim"):
            return default_output

        succ = fun["var"]
        fun2 = fun["fun"]
        if not (isinstance(fun2, dict) and fun2.get("rule") == "fun_elim"):
            return default_output

        zero = fun2["var"]
        fun3 = fun2["fun"]

        if fun3 == "Nat.ind":
            if self.judge(n, "zero"):
                return self.compute(zero)

            if isinstance(n, dict) and n.get("rule") == "fun_elim" and n.get("fun") == "succ":
                k = self.compute(n["var"])
                rec_result = self.compute_elim_nat(fun, k)
                return self.compute(
                    {
                        "rule": "fun_elim",
                        "fun": {"rule": "fun_elim", "fun": succ, "var": k},
                        "var": rec_result,
                    }
                )

        return default_output

    def compute_elim_id(self, fun: Expr, proof: Expr) -> Expr:
        default_output = {"rule": "fun_elim", "fun": fun, "var": proof}

        head, args = self._unwrap_app(fun)
        if head != "Id.ind":
            return default_output

        if len(args) != 5:
            return default_output

        id_type, left, motive, refl_case, right = args
        proof_head, proof_args = self._unwrap_app(proof)
        if proof_head != "refl" or len(proof_args) != 2:
            return default_output

        refl_type, refl_term = proof_args
        if not (self.judge(id_type, refl_type) and self.judge(left, refl_term)):
            return default_output

        if not self.judge(right, left):
            return default_output

        return self.compute(refl_case)

    def compute(self, expression: Expr) -> Expr:
        expression = self.parse(expression) if isinstance(expression, str) else expression

        if isinstance(expression, str):
            info = self.variables.get(expression)
            if info is None or info.definition == "axiom":
                return expression
            return self.compute(info.definition)

        rule = expression["rule"]
        if rule == "fun_form":
            dom = self.compute(expression["dom"])
            new_context = self.copy_with_dummy(expression["var"], dom)
            return {
                "rule": "fun_form",
                "dom": dom,
                "var": expression["var"],
                "cod": new_context.compute(expression["cod"]),
            }

        if rule == "fun_intro":
            dom = self.compute(expression["dom"])
            new_context = self.copy_with_dummy(expression["var"], dom)
            return {
                "rule": "fun_intro",
                "dom": dom,
                "var": expression["var"],
                "body": new_context.compute(expression["body"]),
            }

        if rule == "fun_elim":
            fun = self.compute(expression["fun"])
            var = self.compute(expression["var"])

            if isinstance(fun, str):
                return {"rule": "fun_elim", "fun": fun, "var": var}

            if fun.get("rule") == "fun_intro":
                return self.compute(self.substitute(fun["body"], fun["var"], var))

            if self.judge(self.check(var), "Nat"):
                return self.compute_elim_nat(fun, var)

            if self._is_id_type(self.check(var)):
                return self.compute_elim_id(fun, var)

            return {"rule": "fun_elim", "fun": fun, "var": var}

        return expression

    def check(self, expression: Expr) -> Expr:
        expression = self.parse(expression) if isinstance(expression, str) else expression

        if isinstance(expression, str):
            if expression == "Type":
                return "Type1"
            type_level = self._type_level(expression)
            if type_level is not None:
                return f"Type{type_level + 1}"
            if expression not in self.variables:
                raise ValueError(f"Unknown variable '{expression}'.")
            return self.variables[expression].var_type

        rule = expression["rule"]
        if rule == "fun_form":
            dom = expression["dom"]
            var = expression["var"]
            cod = expression["cod"]

            if not self._is_type_value(self.check(dom)):
                raise ValueError("Domain of function type is not a type.")

            new_context = self.copy_with_dummy(var, dom)
            if not new_context._is_type_value(new_context.check(cod)):
                raise ValueError("Codomain of function type is not a type.")

            return "Type"

        if rule == "fun_intro":
            dom = expression["dom"]
            var = expression["var"]
            body = expression["body"]

            if not self._is_type_value(self.check(dom)):
                raise ValueError("Domain of function introduction is not a type.")

            new_context = self.copy_with_dummy(var, dom)
            body_type = new_context.check(body)
            if not new_context._is_type_value(new_context.check(body_type)):
                raise ValueError("Body of function introduction is not an element of a type.")

            return {"rule": "fun_form", "dom": dom, "var": var, "cod": new_context.check(body)}

        if rule == "fun_elim":
            fun = expression["fun"]
            var = expression["var"]

            fun_type = self.compute(self.check(fun))
            if fun_type.get("rule") != "fun_form":
                raise ValueError(f"{fun} has type {fun_type} but a function type is expected.")

            dom = fun_type["dom"]
            cod = fun_type["cod"]
            fun_var = fun_type["var"]

            if not self.judge(self.check(var), dom):
                raise ValueError(
                    f"Argument {var} in function elimination does not match function domain {dom}."
                )

            return self.substitute(cod, fun_var, var)

        raise ValueError(f"Unknown expression rule '{rule}' for checking.")

    def clean_compute(self, expression: Expr) -> str:
        return self.unparse(self.compute(expression))

    def clean_check(self, expression: Expr) -> str:
        return self.unparse(self.check(expression))

    @staticmethod
    def _both_rule(expr1: Expr, expr2: Expr, rule: Rule) -> bool:
        return (
            isinstance(expr1, dict)
            and isinstance(expr2, dict)
            and expr1.get("rule") == rule
            and expr2.get("rule") == rule
        )

    @staticmethod
    def _unwrap_app(expr: Expr) -> tuple[Expr, list[Expr]]:
        if not isinstance(expr, dict) or expr.get("rule") != "fun_elim":
            return expr, []
        args: list[Expr] = []
        while isinstance(expr, dict) and expr.get("rule") == "fun_elim":
            args.append(expr["var"])
            expr = expr["fun"]
        args.reverse()
        return expr, args

    def _is_id_type(self, expr: Expr) -> bool:
        expr = self.compute(expr)
        head, args = self._unwrap_app(expr)
        return head == "Id" and len(args) == 3

    def _is_type_value(self, expr: Expr) -> bool:
        expr = self.compute(expr) if isinstance(expr, str) else self.compute(expr)
        return isinstance(expr, str) and self._type_level(expr) is not None

    @staticmethod
    def _type_level(name: str) -> int | None:
        if name == "Type":
            return 0
        if name.startswith("Type") and name[4:].isdigit():
            return int(name[4:])
        return None

    @staticmethod
    def _free_vars(expr: Expr) -> set[str]:
        if isinstance(expr, str):
            return {expr}
        rule = expr.get("rule")
        if rule in ("fun_form", "fun_intro"):
            dom_vars = Context._free_vars(expr["dom"])
            body_key = "cod" if rule == "fun_form" else "body"
            body_vars = Context._free_vars(expr[body_key])
            return dom_vars | (body_vars - {expr["var"]})
        if rule == "fun_elim":
            return Context._free_vars(expr["fun"]) | Context._free_vars(expr["var"])
        return set()

    @staticmethod
    def _rename_free(expr: Expr, old: str, new: str) -> Expr:
        if isinstance(expr, str):
            return new if expr == old else expr
        rule = expr.get("rule")
        if rule in ("fun_form", "fun_intro"):
            dom = Context._rename_free(expr["dom"], old, new)
            body_key = "cod" if rule == "fun_form" else "body"
            if expr["var"] == old:
                return {**expr, "dom": dom, body_key: expr[body_key]}
            return {**expr, "dom": dom, body_key: Context._rename_free(expr[body_key], old, new)}
        if rule == "fun_elim":
            return {
                "rule": "fun_elim",
                "fun": Context._rename_free(expr["fun"], old, new),
                "var": Context._rename_free(expr["var"], old, new),
            }
        return expr

    def _fresh_name(self, avoid: set[str]) -> str:
        candidate = 1
        while True:
            name = f"_x{candidate}"
            if name not in avoid:
                return name
            candidate += 1


if __name__ == "__main__":
    c = Context()
    c.define(
        "add",
        "Nat -> Nat -> Nat",
        "(m : Nat) => Nat.ind ((_ : Nat) => Nat -> Nat) ((n : Nat) => n)"
        "((k : Nat) (rec : Nat -> Nat) => (n : Nat) => succ (rec n)) m",
    )

    print(c.clean_check("Nat -> Nat"))

    c.define("one", "Nat", "succ zero")
    c.define("two", "Nat", "succ one")
    c.define("three", "Nat", "succ two")

    print(c.judge("add one three", "add two two"))
    print(c.judge("add one two", "one"))

    print(c.unparse(c.compute("add one two")))

    c.postulate("x", "Nat")
    c.postulate("y", "Nat")
    print(c.judge("add x zero", "x"))
    print(c.judge("add x (succ y)", "succ (add x y)"))

    c.postulate("A", "Type")
    c.postulate("B", "Type")
    c.postulate("C", "Type")
    c.postulate("D", "Type")
    c.define(
        "compose",
        "(B -> C) -> (A -> B) -> (A -> C)",
        "(g : B -> C) => (f : A -> B) => (z : A) => g (f z)",
    )

    c.postulate("f", "A -> B")
    c.postulate("g", "B -> C")
    c.postulate("h", "C -> D")
    print(c.judge("compose h (compose g f)", "compose (compose h g) f"))
    print("see me!!!")
    c = Context()
    c.postulate("A", "Type")
    c.postulate("x", "A")
    term = "Id.ind A x ((y : A) => (_ : Id A x y) => A) x x (refl A x)"
    print(c.judge(term, "x"))          
    print(c.clean_compute(term))       

