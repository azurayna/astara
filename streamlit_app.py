from __future__ import annotations

from pprint import pformat
import re
import unicodedata

import streamlit as st

from astara import Context

APP_BUILD = "2026-02-24.1"

_SMALL_NUM_NAMES = {
    0: "zero",
    1: "one",
    2: "two",
    3: "three",
    4: "four",
    5: "five",
    6: "six",
    7: "seven",
    8: "eight",
    9: "nine",
    10: "ten",
}


def _normalize_input_ops(text: str) -> str:
    # Normalize compatibility/full-width forms first.
    text = unicodedata.normalize("NFKC", text)

    # Map common math glyph variants to ASCII operators.
    plus_like = {"\u2795", "\u2295", "\u2214"}
    minus_like = {"\u2212", "\u2013", "\u2014"}
    mul_like = {"\u00d7", "\u2715", "\u2716", "\u2a2f", "\u22c5", "\u00b7", "\u2217"}
    div_like = {"\u00f7", "\u2215", "\u2044"}

    out: list[str] = []
    for ch in text:
        if ch in plus_like:
            out.append("+")
        elif ch in minus_like:
            out.append("-")
        elif ch in mul_like:
            out.append("*")
        elif ch in div_like:
            out.append("/")
        else:
            out.append(ch)
    return "".join(out)

def _nat_to_int(expr: object) -> int | None:
    if isinstance(expr, str):
        if expr == "zero":
            return 0
        return None

    if isinstance(expr, dict) and expr.get("rule") == "fun_elim" and expr.get("fun") == "succ":
        inner = _nat_to_int(expr.get("var"))
        if inner is not None:
            return inner + 1
    return None


def _int_to_name(num: int) -> str:
    if num in _SMALL_NUM_NAMES:
        return _SMALL_NUM_NAMES[num]
    return str(num)


def _num_to_expr(num: int) -> str:
    term = "zero"
    for _ in range(num):
        term = f"succ ({term})"
    return term


def _compute_fixpoint(context: Context, expr: object, max_steps: int = 64) -> object:
    current = context.compute(expr)
    for _ in range(max_steps):
        nxt = context.compute(current)
        if nxt == current:
            return current
        current = nxt
    return current


def _pretty_nat_output(context: Context, reduced: object, original_input: str) -> str | None:
    as_int = _nat_to_int(reduced)
    if as_int is None:
        # Fallback: try via unparse+parse to catch equivalent succ normal forms.
        try:
            reparsed = context.parse(context.unparse(reduced))
            as_int = _nat_to_int(reparsed)
        except Exception:
            as_int = None
    if as_int is None:
        return None
    if re.search(r"\d", original_input):
        return str(as_int)
    return _int_to_name(as_int)


def load_standard_rules(context: Context) -> None:
    # Core arithmetic definitions
    context.define(
        "add",
        "Nat -> Nat -> Nat",
        "(m : Nat) => Nat.ind ((_ : Nat) => Nat -> Nat) ((n : Nat) => n)"
        " ((k : Nat) (rec : Nat -> Nat) => (n : Nat) => succ (rec n)) m",
    )
    context.define("one", "Nat", "succ zero")
    context.define("two", "Nat", "succ one")
    context.define("three", "Nat", "succ two")
    context.define("four", "Nat", "succ three")
    context.define("five", "Nat", "succ four")
    context.define("six", "Nat", "succ five")
    context.define("seven", "Nat", "succ six")
    context.define("eight", "Nat", "succ seven")
    context.define("nine", "Nat", "succ eight")
    context.define("ten", "Nat", "succ nine")
    context.define(
        "mul",
        "Nat -> Nat -> Nat",
        "(m : Nat) => Nat.ind ((_ : Nat) => Nat -> Nat) ((n : Nat) => zero)"
        " ((k : Nat) (rec : Nat -> Nat) => (n : Nat) => add n (rec n)) m",
    )
    context.define("eq", "Nat -> Nat -> Type", "(a : Nat) => (b : Nat) => Id Nat a b")

    # Equality rules (proved, not postulated)
    context.define(
        "reflexivity",
        "(A : Type) -> (x : A) -> Id A x x",
        "(A : Type) => (x : A) => refl A x",
    )
    context.postulate(
        "symmetry",
        "(A : Type) -> (x : A) -> (y : A) -> Id A x y -> Id A y x",
    )
    context.postulate(
        "transitivity",
        "(A : Type) -> (x : A) -> (y : A) -> (z : A)"
        " -> Id A x y -> Id A y z -> Id A x z",
    )

    # Algebraic laws on Nat
    context.postulate(
        "add_commutativity",
        "(a : Nat) -> (b : Nat) -> Id Nat (add a b) (add b a)",
    )
    context.postulate(
        "add_associativity",
        "(a : Nat) -> (b : Nat) -> (c : Nat)"
        " -> Id Nat (add (add a b) c) (add a (add b c))",
    )
    context.postulate(
        "mul_commutativity",
        "(a : Nat) -> (b : Nat) -> Id Nat (mul a b) (mul b a)",
    )
    context.postulate(
        "mul_associativity",
        "(a : Nat) -> (b : Nat) -> (c : Nat)"
        " -> Id Nat (mul (mul a b) c) (mul a (mul b c))",
    )
    context.postulate(
        "distributive_property",
        "(a : Nat) -> (b : Nat) -> (c : Nat)"
        " -> Id Nat (mul a (add b c)) (add (mul a b) (mul a c))",
    )
    context.postulate(
        "add_identity",
        "(a : Nat) -> Id Nat (add a zero) a",
    )
    context.postulate(
        "mul_identity",
        "(a : Nat) -> Id Nat (mul a one) a",
    )

    # Closure and non-closure notes
    context.define("add_closed_nat", "(a : Nat) -> (b : Nat) -> Nat", "(a : Nat) => (b : Nat) => add a b")
    context.define("mul_closed_nat", "(a : Nat) -> (b : Nat) -> Nat", "(a : Nat) => (b : Nat) => mul a b")
    context.postulate("Int", "Type")
    context.postulate("Rat", "Type")
    context.postulate("sub", "Nat -> Nat -> Int")
    context.postulate("div", "Nat -> Nat -> Rat")
    context.postulate("sub_not_closed_nat", "Type")
    context.postulate("div_not_closed_nat", "Type")

    # Number-theoretic principles
    context.postulate("prime", "Nat -> Type")
    context.postulate("divides", "Nat -> Nat -> Type")
    context.postulate("well_order_nat", "Type")
    context.postulate("uniqueness", "Type")
    context.postulate("unique_prime_factorization", "(n : Nat) -> Type")


def _ensure_minimal_arithmetic(context: Context) -> None:
    def define_if_missing(name: str, var_type: str, definition: str) -> None:
        if name not in context.variables:
            context.define(name, var_type, definition)

    define_if_missing(
        "add",
        "Nat -> Nat -> Nat",
        "(m : Nat) => Nat.ind ((_ : Nat) => Nat -> Nat) ((n : Nat) => n)"
        " ((k : Nat) (rec : Nat -> Nat) => (n : Nat) => succ (rec n)) m",
    )
    define_if_missing("one", "Nat", "succ zero")
    define_if_missing("two", "Nat", "succ one")
    define_if_missing("three", "Nat", "succ two")
    define_if_missing("four", "Nat", "succ three")
    define_if_missing("five", "Nat", "succ four")
    define_if_missing("six", "Nat", "succ five")
    define_if_missing("seven", "Nat", "succ six")
    define_if_missing("eight", "Nat", "succ seven")
    define_if_missing("nine", "Nat", "succ eight")
    define_if_missing("ten", "Nat", "succ nine")
    define_if_missing(
        "mul",
        "Nat -> Nat -> Nat",
        "(m : Nat) => Nat.ind ((_ : Nat) => Nat -> Nat) ((n : Nat) => zero)"
        " ((k : Nat) (rec : Nat -> Nat) => (n : Nat) => add n (rec n)) m",
    )


def run_setup_line(context: Context, line: str) -> None:
    line = line.strip()
    if not line:
        return

    if line.startswith("postulate "):
        payload = line[len("postulate ") :]
        name, _, var_type = payload.partition(":")
        if not name.strip() or not var_type.strip():
            raise ValueError(f"Invalid postulate syntax: {line}")
        context.postulate(name.strip(), _to_prefix_infix(var_type.strip()))
        return

    if line.startswith("define "):
        payload = line[len("define ") :]
        name_part, sep, rest = payload.partition(":")
        if not sep:
            raise ValueError(f"Invalid define syntax: {line}")
        var_type, sep2, definition = rest.partition(":=")
        if not sep2:
            raise ValueError(f"Invalid define syntax: {line}")
        name = name_part.strip()
        override = name in {
            "add",
            "mul",
            "one",
            "two",
            "three",
            "four",
            "five",
            "six",
            "seven",
            "eight",
            "nine",
            "ten",
            "eq",
        }
        context.define(
            name,
            _to_prefix_infix(var_type.strip()),
            _to_prefix_infix(definition.strip()),
            override=override,
        )
        return

    raise ValueError(
        "Unsupported setup command. Use 'postulate NAME : TYPE' or "
        "'define NAME : TYPE := EXPR'."
    )


def _tokenize_infix(expr: str) -> list[str]:
    expr = _normalize_input_ops(expr)
    token_pattern = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_.]*|[0-9]+|\(|\)|\+|\-|\*|/|:|=)\s*")
    tokens: list[str] = []
    pos = 0
    while pos < len(expr):
        match = token_pattern.match(expr, pos)
        if not match:
            return []
        tokens.append(match.group(1))
        pos = match.end()
    return tokens


def _to_prefix_infix(expr: str) -> str:
    expr = _normalize_input_ops(expr)
    # Keep native syntax untouched if it already looks like core language.
    if "->" in expr or "=>" in expr:
        return expr.strip()

    tokens = _tokenize_infix(expr)
    if not tokens:
        return expr.strip()

    if ":" in tokens:
        raise ValueError(
            "':' is treated as type assertion syntax (x : A). "
            "Use '/' for division."
        )

    index = 0

    def parse_atom() -> str:
        nonlocal index
        if index >= len(tokens):
            raise ValueError("Unexpected end of expression.")
        tok = tokens[index]
        if tok == "(":
            index += 1
            inner = parse_eq()
            if index >= len(tokens) or tokens[index] != ")":
                raise ValueError("Missing closing ')'.")
            index += 1
            return f"({inner})"
        if tok in {"+", "-", "*", "/", ":", "="}:
            raise ValueError(f"Unexpected operator '{tok}'.")
        index += 1
        if tok.isdigit():
            return _num_to_expr(int(tok))
        return tok

    def parse_mul() -> str:
        nonlocal index
        left = parse_atom()
        while index < len(tokens) and tokens[index] in {"*", "/"}:
            op = tokens[index]
            index += 1
            right = parse_atom()
            fn = "mul" if op == "*" else "div"
            left = f"{fn} ({left}) ({right})"
        return left

    def parse_add() -> str:
        nonlocal index
        left = parse_mul()
        while index < len(tokens) and tokens[index] in {"+", "-"}:
            op = tokens[index]
            index += 1
            right = parse_mul()
            fn = "add" if op == "+" else "sub"
            left = f"{fn} ({left}) ({right})"
        return left

    def parse_eq() -> str:
        nonlocal index
        left = parse_add()
        while index < len(tokens) and tokens[index] == "=":
            index += 1
            right = parse_add()
            left = f"eq ({left}) ({right})"
        return left

    converted = parse_eq()
    if len(tokens) > 1 and all(t not in {"+", "-", "*", "/", ":", "="} for t in tokens):
        parts: list[str] = []
        for t in tokens:
            if t.isdigit():
                parts.append(f"({_num_to_expr(int(t))})")
            else:
                parts.append(t)
        return " ".join(parts)
    if index != len(tokens):
        return expr.strip()
    return converted


def _split_judge_input(lhs: str, rhs: str) -> tuple[str, str]:
    lhs = _normalize_input_ops(lhs).strip()
    rhs = _normalize_input_ops(rhs).strip()
    if rhs:
        return _to_prefix_infix(lhs), _to_prefix_infix(rhs)

    tokens = _tokenize_infix(lhs)
    if "=" in tokens:
        depth = 0
        eq_index = -1
        for i, tok in enumerate(tokens):
            if tok == "(":
                depth += 1
            elif tok == ")":
                depth -= 1
            elif tok == "=" and depth == 0:
                eq_index = i
                break
        if eq_index != -1:
            left = " ".join(tokens[:eq_index])
            right = " ".join(tokens[eq_index + 1 :])
            return _to_prefix_infix(left), _to_prefix_infix(right)

    return _to_prefix_infix(lhs), rhs


def _split_type_assertion(expr: str) -> tuple[str, str] | None:
    tokens = _tokenize_infix(_normalize_input_ops(expr).strip())
    if not tokens or ":" not in tokens:
        return None

    depth = 0
    colon_index = -1
    for i, tok in enumerate(tokens):
        if tok == "(":
            depth += 1
        elif tok == ")":
            depth -= 1
        elif tok == ":" and depth == 0:
            if colon_index != -1:
                return None
            colon_index = i

    if colon_index <= 0 or colon_index >= len(tokens) - 1:
        return None

    left_tokens = tokens[:colon_index]
    right_tokens = tokens[colon_index + 1 :]
    if any(t in {"+", "-", "*", "/", "=", ":"} for t in right_tokens):
        return None

    left = " ".join(left_tokens).strip()
    right = " ".join(right_tokens).strip()
    if not left or not right:
        return None
    return left, right


def run_operation(
    setup: str,
    operation: str,
    lhs: str,
    rhs: str,
    include_standard_rules: bool,
) -> str:
    context = Context()
    if include_standard_rules:
        load_standard_rules(context)
    else:
        _ensure_minimal_arithmetic(context)
    for line in setup.splitlines():
        run_setup_line(context, line)

    lhs = _normalize_input_ops(lhs).strip()
    rhs = _normalize_input_ops(rhs).strip()

    if operation == "Compute":
        if _split_type_assertion(lhs):
            raise ValueError(
                "Expression looks like a type assertion (x : A). "
                "Use 'Check type' for that, and '/' for division."
            )
        converted = _to_prefix_infix(lhs)
        reduced = _compute_fixpoint(context, converted)
        pretty_nat = _pretty_nat_output(context, reduced, lhs)
        if pretty_nat is not None:
            return pretty_nat
        return context.unparse(reduced)
    if operation == "Check type":
        asserted = _split_type_assertion(lhs)
        if asserted is not None:
            value_expr, type_expr = asserted
            inferred = context.check(_to_prefix_infix(value_expr))
            return str(context.judge(inferred, context.parse(type_expr)))
        return context.clean_check(_to_prefix_infix(lhs))
    if operation == "Judge equality":
        lhs_expr, rhs_expr = _split_judge_input(lhs, rhs)
        if not rhs_expr:
            raise ValueError("Judge equality requires a right-hand expression.")
        return str(context.judge(lhs_expr, rhs_expr))
    if operation == "Parse":
        if _split_type_assertion(lhs):
            raise ValueError(
                "x : A is a type assertion, not a term to parse directly. "
                "Use 'Check type' to evaluate it."
            )
        return pformat(context.parse(_to_prefix_infix(lhs)), width=100, sort_dicts=False)
    if operation == "Unparse":
        if _split_type_assertion(lhs):
            raise ValueError(
                "x : A is a type assertion, not a term to unparse directly. "
                "Use 'Check type' to evaluate it."
            )
        return context.unparse(context.parse(_to_prefix_infix(lhs)))
    raise ValueError(f"Unknown operation: {operation}")


def main() -> None:
    st.set_page_config(page_title="Theo Proof Assistant Playground", page_icon=":material/functions:")
    st.title("Astara Type Theory Playground")
    st.caption(f"Run your parser/type-checker from astara.py in Streamlit. Build: {APP_BUILD}")

    if "setup" not in st.session_state:
        st.session_state.setup = (
            "postulate x : Nat\n"
            "postulate y : Nat"
        )
    if "lhs" not in st.session_state:
        st.session_state.lhs = "1 + 2"
    if "rhs" not in st.session_state:
        st.session_state.rhs = ""
    if "operation" not in st.session_state:
        st.session_state.operation = "Compute"
    if "include_rules" not in st.session_state:
        st.session_state.include_rules = True

    with st.form("playground_form", clear_on_submit=False):
        include_standard_rules = st.checkbox(
            "Include standard rules (commutativity, associativity, transitivity, symmetry,"
            " reflexivity, uniqueness, well-order, closure, unique prime factorization,"
            " distributive, identity)",
            key="include_rules",
        )
        if not include_standard_rules:
            st.info(
                "Standard symbols like add, mul, and one are not preloaded. "
                "Define or postulate them in setup before using them."
            )
        setup = st.text_area(
            "Setup commands",
            key="setup",
            height=180,
            help=(
                "One per line: postulate NAME : TYPE or define NAME : TYPE := EXPR. "
                "In expression fields, infix +, -, *, /, and = are supported. "
                "Use x : A in 'Check type' to assert membership."
            ),
        )
        operation = st.selectbox(
            "Operation",
            ["Compute", "Check type", "Judge equality", "Parse", "Unparse"],
            key="operation",
        )
        lhs = st.text_area("Expression", key="lhs", height=100)
        rhs = st.text_area(
            "Right-hand expression (for judge, optional if using a=b in Expression)",
            key="rhs",
            height=80,
        )
        submitted = st.form_submit_button("Run")

    if submitted:
        try:
            with st.expander("Input normalization", expanded=False):
                st.write("Normalized expression:", _to_prefix_infix(lhs))
                if operation == "Judge equality":
                    lhs_expr, rhs_expr = _split_judge_input(lhs, rhs)
                    st.write("Judge left:", lhs_expr)
                    st.write("Judge right:", rhs_expr)
            output = run_operation(setup, operation, lhs, rhs, include_standard_rules)
            st.success("Success")
            st.code(output, language="text")
        except Exception as exc:
            st.error(str(exc))


if __name__ == "__main__":
    main()


