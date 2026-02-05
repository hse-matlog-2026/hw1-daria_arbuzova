# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5
    def convert(f: Formula) -> Formula:
        if is_variable(f.root):
            return f

        left_converted = None
        right_converted = None
        
        if f.first:
            left_converted = convert(f.first)
        if f.second:
            right_converted = convert(f.second)

        if f.root == '~':
            return Formula('~', left_converted)
        
        elif f.root == '&' or f.root == '|':
            return Formula(f.root, left_converted, right_converted)
        
        elif f.root == 'T':
            p = Formula('p')
            return Formula('~', Formula('&', p, Formula('~', p)))
        
        elif f.root == 'F':
            p = Formula('p')
            return Formula('&', p, Formula('~', p))
        
        elif f.root == '->':
            return Formula('|', Formula('~', left_converted), right_converted)
        
        elif f.root == '+':
            left_and_not_right = Formula('&', left_converted, Formula('~', right_converted))
            not_left_and_right = Formula('&', Formula('~', left_converted), right_converted)
            return Formula('|', left_and_not_right, not_left_and_right)
        
        elif f.root == '<->':
            left_impl = Formula('|', Formula('~', left_converted), right_converted)
            right_impl = Formula('|', Formula('~', right_converted), left_converted)
            return Formula('&', left_impl, right_impl)
        
        elif f.root == '-&':
            return Formula('~', Formula('&', left_converted, right_converted))
        
        elif f.root == '-|':
            return Formula('~', Formula('|', left_converted, right_converted))
        
        else:
            raise ValueError(f"Unsupported operator: {f.root}")
    
    return convert(formula)

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    formula_not_and_or = to_not_and_or(formula)
    
    def replace_or(f: Formula) -> Formula:
        if is_variable(f.root):
            return f
        
        if f.root == '~':
            return Formula('~', replace_or(f.first))
        
        if f.root == '&':
            return Formula('&', replace_or(f.first), replace_or(f.second))
        
        if f.root == '|':
            A = replace_or(f.first)
            B = replace_or(f.second)
            return Formula('~', Formula('&', Formula('~', A), Formula('~', B)))
        
        return f
    
    return replace_or(formula_not_and_or)

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    
    formula_not_and = to_not_and(formula)
    
    def replace_with_nand(f: Formula) -> Formula:
        if is_variable(f.root):
            return f
        
        if f.root == '~':
            A = replace_with_nand(f.first)
            return Formula('-&', A, A)
        
        if f.root == '&':
            A = replace_with_nand(f.first)
            B = replace_with_nand(f.second)
            nand_AB = Formula('-&', A, B)
            return Formula('-&', nand_AB, nand_AB)
        
        return f
    
    return replace_with_nand(formula_not_and)

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    formula_not_and_or = to_not_and_or(formula)
    
    def replace_and_or(f: Formula) -> Formula:
        if is_variable(f.root):
            return f
        
        if f.root == '~':
            return Formula('~', replace_and_or(f.first))
        
        if f.root == '&':
            A = replace_and_or(f.first)
            B = replace_and_or(f.second)
            return Formula('~', Formula('->', A, Formula('~', B)))
        
        if f.root == '|':
            A = replace_and_or(f.first)
            B = replace_and_or(f.second)
            return Formula('->', Formula('~', A), B)
        
        if f.root == '->':
            return Formula('->', replace_and_or(f.first), replace_and_or(f.second))
        
        return f
    
    return replace_and_or(formula_not_and_or)

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
    formula_implies_not = to_implies_not(formula)

    def replace_not(f: Formula) -> Formula:
        if is_variable(f.root):
            return f
        
        if f.root == '~':

            A = replace_not(f.first)
            return Formula('->', A, Formula('F'))
        
        if f.root == '->':
            return Formula('->', replace_not(f.first), replace_not(f.second))
        
        return f
    
    return replace_not(formula_implies_not)

