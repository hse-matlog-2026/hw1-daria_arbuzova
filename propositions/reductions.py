# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2025
# File name: propositions/reductions.py

"""Reduction between computational search problems."""

from __future__ import annotations
from typing import AbstractSet, Mapping, Tuple, Union

from propositions.syntax import *
from propositions.semantics import *

#: A graph on a vertex set of the form ``(1,``...\ ``,``\ `n_vertices`\ ``)``,
#: represented by the number of vertices `n_vertices` and a set of edges over
#: the vertices.
Graph = Tuple[int, AbstractSet[Tuple[int, int]]] 

def is_graph(graph: Graph) -> bool:
    """Checks if the given data structure is a valid representation of a graph.

    Parameters:
        graph: data structure to check.

    Returns:
        ``True`` if the given data structure is a valid representation of a
        graph, ``False`` otherwise.
    """
    (n_vertices, edges) = graph
    for edge in edges:
        for vertex in edge:
            if not 1 <= vertex <= n_vertices:
                return False
        if edge[0] == edge[1]:
            return False
    return True

def is_valid_3coloring(graph: Graph, coloring: Mapping[int, int]) -> bool:
    """Checks whether the given coloring is a valid coloring of the given graph
    by the colors 1, 2, and 3.

    Parameters:
        graph: graph to check.
        coloring: mapping from the vertices of the given graph to colors,
            to check.

    Returns:
        ``True`` if the given coloring is a valid coloring of the given graph by
        the colors 1, 2, and 3; ``False`` otherwise.
    """
    assert is_graph(graph)
    (n_vertices, edges) = graph
    for vertex in range(1, n_vertices + 1):
        if vertex not in coloring.keys() or coloring[vertex] not in {1, 2, 3}:
            return False
    for edge in edges:
        if coloring[edge[0]] == coloring[edge[1]]:
            return False
    return True

def graph3coloring_to_formula(graph: Graph) -> Formula:
    """Efficiently reduces the 3-coloring problem of the given graph into a
    satisfiability problem.

    Parameters:
        graph: graph whose 3-coloring problem to reduce.
       
    Returns:
        A propositional formula that is satisfiable if and only if the given
        graph is 3-colorable.
    """
    assert is_graph(graph)
    n_vertices, edges = graph
    
    formulas = []
    
    for v in range(1, n_vertices + 1):
        vertex_formulas = []
        for c in range(1, 4):
            var_name = f"x{v}_{c}"
            vertex_formulas.append(Formula(var_name))
        formula = Formula("|", vertex_formulas[0], vertex_formulas[1])
        formula = Formula("|", formula, vertex_formulas[2])
        formulas.append(formula)

    for v in range(1, n_vertices + 1):
        for c1 in range(1, 4):
            for c2 in range(c1 + 1, 4):
                var1 = f"x{v}_{c1}"
                var2 = f"x{v}_{c2}"
                formula = Formula("|", 
                                 Formula("~", Formula(var1)),
                                 Formula("~", Formula(var2)))
                formulas.append(formula)
    
    for u, v in edges:
        for c in range(1, 4):
            var_u = f"x{u}_{c}"
            var_v = f"x{v}_{c}"
            formula = Formula("|",
                             Formula("~", Formula(var_u)),
                             Formula("~", Formula(var_v)))
            formulas.append(formula)

    if not formulas:
        return Formula("T")
    
    result = formulas[0]
    for formula in formulas[1:]:
        result = Formula("&", result, formula)
    
    return result
    # Optional Task 2.10a

def assignment_to_3coloring(graph: Graph, assignment: Model) -> \
        Mapping[int, int]:
    """Efficiently transforms an assignment to the formula corresponding to the
    3-coloring problem of the given graph, to a 3-coloring of the given graph so
    that the 3-coloring is valid if and only if the given assignment is
    satisfying.

    Parameters:
        graph: graph to produce a 3-coloring for.
        assignment: assignment to the variable names of the formula returned by
            `graph3coloring_to_formula`\\ ``(``\\ `graph`\\ ``)``.

    Returns:
        A 3-coloring of the given graph by the colors 1, 2, and 3 that is valid
        if and only if the given assignment satisfies the formula
        `graph3coloring_to_formula`\\ ``(``\\ `graph`\\ ``)``.
    """
    assert is_graph(graph)
    formula = graph3coloring_to_formula(graph)
    assert evaluate(formula, assignment)
            
    coloring = {}

    print("testing git")

    for v in range(1, n_vertices + 1):
        for c in range(1, 4):
            var_name = f"x{v}_{c}"
            if assignment.get(var_name, False):
                coloring[v] = c
                break
        else:
            raise ValueError(f"No color assigned to vertex {v} in satisfying assignment")
    assert is_valid_3coloring(graph, coloring)
    
    return coloring
    # Optional Task 2.10b

def tricolor_graph(graph: Graph) -> Union[Mapping[int, int], None]:
    """Computes a 3-coloring of the given graph.

    Parameters:
        graph: graph to 3-color.

    Returns:
        An arbitrary 3-coloring of the given graph if it is 3-colorable,
        ``None`` otherwise.
    """
    assert is_graph(graph)
    formula = graph3coloring_to_formula(graph)
    for assignment in all_models(list(formula.variables())):
        if evaluate(formula, assignment):
            return assignment_to_3coloring(graph, assignment)
    return None

