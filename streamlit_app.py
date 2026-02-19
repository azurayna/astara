from __future__ import annotations

from pprint import pformat

import streamlit as st

from astara import Context


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


def run_operation(setup: str, operation: str, lhs: str, rhs: str) -> str:
    context = Context()
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
    st.set_page_config(page_title="Astara Playground", page_icon=":material/functions:")
    st.title("Astara Type Theory Playground")
    st.caption("Run your parser/type-checker from astara.py in Streamlit.")

    if "setup" not in st.session_state:
        st.session_state.setup = (
            "define add : Nat -> Nat -> Nat := "
            "(m : Nat) => Nat.ind ((_ : Nat) => Nat -> Nat) ((n : Nat) => n) "
            "((k : Nat) (rec : Nat -> Nat) => (n : Nat) => succ (rec n)) m\n"
            "define one : Nat := succ zero\n"
            "define two : Nat := succ one"
        )
    if "lhs" not in st.session_state:
        st.session_state.lhs = "add one two"
    if "rhs" not in st.session_state:
        st.session_state.rhs = ""
    if "operation" not in st.session_state:
        st.session_state.operation = "Compute"

    with st.form("playground_form", clear_on_submit=False):
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
            output = run_operation(setup, operation, lhs, rhs)
            st.success("Success")
            st.code(output, language="text")
        except Exception as exc:
            st.error(str(exc))


if __name__ == "__main__":
    main()
