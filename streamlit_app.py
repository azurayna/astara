from __future__ import annotations

from pprint import pformat

import streamlit as st

from astara import Context


def load_standard_rules(context: Context) -> None:
    # basic nat
    context.define(
        "add",
        "Nat -> Nat -> Nat",
        "(m : Nat) => Nat.ind ((_ : Nat) => Nat -> Nat) ((n : Nat) => n)"
        " ((k : Nat) (rec : Nat -> Nat) => (n : Nat) => succ (rec n)) m",
    )
    context.define("one", "Nat", "succ zero")
    context.define(
        "mul",
        "Nat -> Nat -> Nat",
        "(m : Nat) => Nat.ind ((_ : Nat) => Nat -> Nat) ((n : Nat) => zero)"
        " ((k : Nat) (rec : Nat -> Nat) => (n : Nat) => add n (rec n)) m",
    )

    # equality (no univalence yet)
    context.postulate("reflexivity", "(A : Type) -> (x : A) -> Id A x x")
    context.postulate(
        "symmetry",
        "(A : Type) -> (x : A) -> (y : A) -> Id A x y -> Id A y x",
    )
    context.postulate(
        "transitivity",
        "(A : Type) -> (x : A) -> (y : A) -> (z : A)"
        " -> Id A x y -> Id A y z -> Id A x z",
    )

    # nat laws
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

    # closure and nonclosure
    context.postulate("add_closed_nat", "(a : Nat) -> (b : Nat) -> Nat")
    context.postulate("mul_closed_nat", "(a : Nat) -> (b : Nat) -> Nat")
    context.postulate("Int", "Type")
    context.postulate("Rat", "Type")
    context.postulate("sub", "Nat -> Nat -> Int")
    context.postulate("div", "Nat -> Nat -> Rat")
    context.postulate("sub_not_closed_nat", "Type")
    context.postulate("div_not_closed_nat", "Type")

    # number theoretic concepts
    context.postulate("prime", "Nat -> Type")
    context.postulate("divides", "Nat -> Nat -> Type")
    context.postulate("well_order_nat", "Type")
    context.postulate("uniqueness", "Type")
    context.postulate("unique_prime_factorization", "(n : Nat) -> Type")


def run_setup_line(context: Context, line: str) -> None:
    line = line.strip()
    if not line:
        return

    if line.startswith("postulate "):
        payload = line[len("postulate ") :]
        name, _, var_type = payload.partition(":")
        if not name.strip() or not var_type.strip():
            raise ValueError(f"Invalid postulate syntax: {line}")
        context.postulate(name.strip(), var_type.strip())
        return

    if line.startswith("define "):
        payload = line[len("define ") :]
        name_part, sep, rest = payload.partition(":")
        if not sep:
            raise ValueError(f"Invalid define syntax: {line}")
        var_type, sep2, definition = rest.partition(":=")
        if not sep2:
            raise ValueError(f"Invalid define syntax: {line}")
        context.define(name_part.strip(), var_type.strip(), definition.strip())
        return

    raise ValueError(
        "Unsupported setup command. Use 'postulate NAME : TYPE' or "
        "'define NAME : TYPE := EXPR'."
    )


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
    for line in setup.splitlines():
        run_setup_line(context, line)

    lhs = lhs.strip()
    rhs = rhs.strip()

    if operation == "Compute":
        return context.clean_compute(lhs)
    if operation == "Check type":
        return context.clean_check(lhs)
    if operation == "Judge equality":
        if not rhs:
            raise ValueError("Judge equality requires a right-hand expression.")
        return str(context.judge(lhs, rhs))
    if operation == "Parse":
        return pformat(context.parse(lhs), width=100, sort_dicts=False)
    if operation == "Unparse":
        return context.unparse(context.parse(lhs))
    raise ValueError(f"Unknown operation: {operation}")


def main() -> None:
    st.set_page_config(page_title="Theo Proof Assistant Playground", page_icon=":material/functions:")
    st.title(";* Theo the Proof Assistant")
    st.caption("A simple proof assistant for learning and experimentation.")

    if "setup" not in st.session_state:
        st.session_state.setup = (
            "define two : Nat := succ one\n"
            "define three : Nat := succ two"
        )
    if "lhs" not in st.session_state:
        st.session_state.lhs = "add one two"
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
            help="One per line: postulate NAME : TYPE or define NAME : TYPE := EXPR",
        )
        operation = st.selectbox(
            "Operation",
            ["Compute", "Check type", "Judge equality", "Parse", "Unparse"],
            key="operation",
        )
        lhs = st.text_area("Expression", key="lhs", height=100)
        rhs = st.text_area("Right-hand expression (for judge)", key="rhs", height=80)
        submitted = st.form_submit_button("Run")

    if submitted:
        try:
            output = run_operation(setup, operation, lhs, rhs, include_standard_rules)
            st.success("Success")
            st.code(output, language="text")
        except Exception as exc:
            st.error(str(exc))


if __name__ == "__main__":
    main()
