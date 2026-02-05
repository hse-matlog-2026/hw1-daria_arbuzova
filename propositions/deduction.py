# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2025
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *

def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` to a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\\ `antecedent`\\ ``->``\\ `consequent`\\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\\ `antecedent`\\ ``->``\\ `consequent`\\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a
                      
    implication_rule = InferenceRule(
        [], 
        Formula('->', antecedent_proof.statement.conclusion, consequent)
    )
    
    specialization_map = conditional.specialization_map(implication_rule)
    specialized_conditional = conditional.specialize(specialization_map)

    implication_proof = Proof(
        implication_rule,
        antecedent_proof.rules.union({MP, conditional}),
        [
            Proof.Line(specialized_conditional.conclusion, specialized_conditional, [])
        ]
    )

    antecedent_line = len(antecedent_proof.lines) - 1  # последняя строка proof для antecedent
    implication_line = antecedent_line + 1  # строка после proof для antecedent
    
    lines = []
    
    for line in antecedent_proof.lines:
        lines.append(line)
    
    lines.append(Proof.Line(
        specialized_conditional.conclusion,
        specialized_conditional,
        []
    ))
    
    lines.append(Proof.Line(
        consequent,
        MP,
        [antecedent_line, implication_line]
    ))
    
    rules = antecedent_proof.rules.union({MP, conditional})
    
    new_statement = InferenceRule(
        antecedent_proof.statement.assumptions,
        consequent
    )
    
    return Proof(new_statement, rules, lines)

def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulas `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``'(``\\ `antecedent1`\\ ``->(``\\ `antecedent2`\\ ``->``\\ `consequent`\\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\\ `antecedent1`\\ ``->(``\\ `antecedent2`\\ ``->``\\ `consequent`\\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `double_conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)
    # Task 5.3b
    
    double_implication_rule = InferenceRule(
        [],
        Formula('->', antecedent1_proof.statement.conclusion,
                Formula('->', antecedent2_proof.statement.conclusion, consequent))
    )

    specialization_map = double_conditional.specialization_map(double_implication_rule)
    specialized_double_conditional = double_conditional.specialize(specialization_map)

    total_lines_from_proof1 = len(antecedent1_proof.lines)
    total_lines_from_proof2 = len(antecedent2_proof.lines)

    lines = []
    
    for line in antecedent1_proof.lines:
        lines.append(line)
    
    for line in antecedent2_proof.lines:
        if not line.is_assumption():
            new_assumptions = tuple(a + total_lines_from_proof1 for a in line.assumptions)
            lines.append(Proof.Line(line.formula, line.rule, new_assumptions))
        else:
            lines.append(line)
    
    lines.append(Proof.Line(
        specialized_double_conditional.conclusion,
        specialized_double_conditional,
        []
    ))
    
    lines.append(Proof.Line(
        Formula('->', antecedent2_proof.statement.conclusion, consequent),
        MP,
        [total_lines_from_proof1 - 1,
         total_lines_from_proof1 + total_lines_from_proof2]
    ))
    
    lines.append(Proof.Line(
        consequent,
        MP,
        [total_lines_from_proof1 + total_lines_from_proof2 - 1,
         total_lines_from_proof1 + total_lines_from_proof2 + 1]
    ))
    
    rules = antecedent1_proof.rules.union({MP, double_conditional})
    
    new_statement = InferenceRule(
        antecedent1_proof.statement.assumptions,
        consequent
    )
    
    return Proof(new_statement, rules, lines)

def remove_assumption(proof: Proof) -> Proof:
    """Converts the given proof of some `conclusion` formula, the last
    assumption of which is an assumption `assumption`, to a proof of
    ``'(``\\ `assumption`\\ ``->``\\ `conclusion`\\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of ``'(``\\ `assumption`\\ ``->``\\ `conclusion`\\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """        
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4
    assumption = proof.statement.assumptions[-1]
    conclusion = proof.statement.conclusion
    
    new_lines = []
  
    for i, line in enumerate(proof.lines):
        formula = line.formula
        
        if line.is_assumption():
            if formula == assumption:
                new_lines.append(Proof.Line(
                    Formula('->', assumption, assumption),
                    I0,
                    []
                ))
            else:
                new_lines.append(Proof.Line(
                    Formula('->', formula, Formula('->', assumption, formula)),
                    I1,
                    []
                ))
        
        else:
            rule_used = line.rule
            
            if rule_used == MP:

                phi_line = line.assumptions[0]
                implication_line = line.assumptions[1]

                d_formula = Formula('->',
                                   Formula('->', assumption, 
                                          Formula('->', 
                                                 proof.lines[phi_line].formula,
                                                 proof.lines[implication_line].formula)),
                                   Formula('->',
                                          Formula('->', assumption, proof.lines[phi_line].formula),
                                          Formula('->', assumption, formula)))

                new_lines.append(Proof.Line(d_formula, D, []))
                
            else:
                new_lines.append(Proof.Line(formula, rule_used, []))

                i1_formula = Formula('->', formula, 
                                    Formula('->', assumption, formula))
                new_lines.append(Proof.Line(i1_formula, I1, []))

                mp_line1 = len(new_lines) - 2  # строка с ψ
                mp_line2 = len(new_lines) - 1  # строка с I1
                new_lines.append(Proof.Line(
                    Formula('->', assumption, formula),
                    MP,
                    [mp_line1, mp_line2]
                ))
    
    new_statement = InferenceRule(
        proof.statement.assumptions[:-1],  # все кроме последнего
        Formula('->', assumption, conclusion)
    )

    rules = proof.rules.union({MP, I0, I1, D})
    return Proof(new_statement, rules, [])

def prove_from_opposites(proof_of_affirmation: Proof,
                         proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\\ `affirmation`\\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\\ `affirmation`\\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.
        conclusion: formula to prove.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6
    affirmation = proof_of_affirmation.statement.conclusion
    negation = proof_of_negation.statement.conclusion

    i2_formula = Formula('->', 
                        Formula('~', affirmation),
                        Formula('->', affirmation, conclusion))

    i2_specialized = InferenceRule([], i2_formula)
    
    lines = []
    
    offset_affirmation = 0
    for line in proof_of_affirmation.lines:
        lines.append(line)
    offset_affirmation = len(lines) - 1

    offset_negation = len(lines)
    for i, line in enumerate(proof_of_negation.lines):
        if line.is_assumption():
            lines.append(line)
        else:
            new_assumptions = tuple(a + offset_affirmation + 1 for a in line.assumptions)
            lines.append(Proof.Line(line.formula, line.rule, new_assumptions))
    offset_negation_end = len(lines) - 1

    lines.append(Proof.Line(i2_formula, I2, []))
    i2_line = len(lines) - 1

    lines.append(Proof.Line(
        Formula('->', affirmation, conclusion),
        MP,
        [offset_negation_end, i2_line]
    ))

    lines.append(Proof.Line(
        conclusion,
        MP,
        [offset_affirmation, len(lines) - 1]
    ))

    rules = proof_of_affirmation.rules.union({MP, I2})

    new_statement = InferenceRule(
        proof_of_affirmation.statement.assumptions,
        conclusion
    )
    
    return Proof(new_statement, rules, lines)

def prove_by_way_of_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\\ `formula`\\ ``'``, to a proof of `formula` from the
    same assumptions except ``'~``\\ `formula`\\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\\ `formula`\\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
    negation = proof.statement.assumptions[-1]
    formula = negation.first 
    
    new_statement = InferenceRule(
        proof.statement.assumptions[:-1],  # все кроме последнего
        formula
    )
    
    return Proof(new_statement, rules, [])

