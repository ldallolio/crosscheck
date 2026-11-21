package net.sf.metacad.revenge.constraint;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.Stack;

import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.CodeExpressionVisitor;
import net.sf.metacad.revenge.expression.MultipleConditionedExpression;
import net.sf.metacad.revenge.expression.PlaceholderExpression;
import net.sf.metacad.revenge.expression.SymbolicExpression;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.expression.arithmetic.ArithmeticVariableReference;
import net.sf.metacad.revenge.expression.arithmetic.BinaryArithmeticOperator;
import net.sf.metacad.revenge.expression.arithmetic.BinaryExtremaExpression;
import net.sf.metacad.revenge.expression.arithmetic.BinaryIntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.ExtremumOperator;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.arithmetic.MinusIntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.UnaryArithmeticExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanOperator;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonOperator;
import net.sf.metacad.revenge.expression.logic.NotExpression;
import net.sf.metacad.revenge.type.NumericType;

public class SymbolicConstraintVisitor implements CodeExpressionVisitor, ConstraintSolver {

	private final Map<String, String> variableBindings = new LinkedHashMap<>();

	private final Map<String, String> functionBindings = new LinkedHashMap<>();

	private final Stack<CodeExpression> constraints = new Stack<>();

	private final List<CodeExpression> model = new ArrayList<>();

	private final Map<String, VariableReference> constraintUnknowns = new LinkedHashMap<>();

	private final Map<String, SymbolicExpression> symbols = new LinkedHashMap<>();

	private VariableReference tominimize;

	@Override
	public void arithmeticCondition(CodeExpression expression) {
		if (expression instanceof IntegerValueExpression) {
			constraints.push(expression);
		} else if (expression instanceof BinaryIntegerExpression) {
			BinaryIntegerExpression binaryArithmeticExpression = (BinaryIntegerExpression) expression;
			binaryArithmeticExpression.leftSide.accept(this);
			CodeExpression leftside = constraints.pop();
			binaryArithmeticExpression.rightSide.accept(this);
			CodeExpression rightside = constraints.pop();
			CodeExpression constraint = BinaryIntegerExpression.create(binaryArithmeticExpression.operator, leftside,
					rightside);
			constraints.push(constraint);
		} else if (expression instanceof MinusIntegerExpression) {
			MinusIntegerExpression minusExpression = (MinusIntegerExpression) expression;
			minusExpression.rightSide.accept(this);
			CodeExpression rightSide = constraints.pop();
			CodeExpression constraint = MinusIntegerExpression.create(rightSide);
			constraints.push(constraint);
		} else {
			throw new UnsupportedOperationException("not yet implemented");
		}
	}

	@Override
	public void compare(ComparisonExpression expression) {
		expression.leftSide.accept(this);
		CodeExpression leftside = constraints.pop();
		expression.rightSide.accept(this);
		CodeExpression rightside = constraints.pop();
		CodeExpression constraint = ComparisonExpression.create(expression.operator, leftside, rightside);
		constraints.push(constraint);
	}

	@Override
	public void compose(BinaryBooleanExpression expression) {
		expression.getLeftSide().accept(this);
		CodeExpression leftside = constraints.pop();
		expression.getRightSide().accept(this);
		CodeExpression rightside = constraints.pop();
		CodeExpression constraint = BinaryBooleanExpression.create(expression.operator, (BooleanExpression) leftside,
				(BooleanExpression) rightside);
		constraints.push(constraint);
	}

	@Override
	public void follow(CodeExpression expression) {
		expression.accept(this);
	}

	@Override
	public void negate(NotExpression negated) {
		negated.rightSide.accept(this);
		CodeExpression rightside = constraints.pop();
		BooleanExpression constraint = NotExpression.create((BooleanExpression) rightside);
		constraints.push(constraint);
	}

	@Override
	public void repeat(CodeExpression expression, IntegerExpression times, Map<String, CodeExpression> initialValues) {
		expression.repeat(times, this, initialValues);
	}

	@Override
	public void useVariable(PlaceholderExpression placeholder) {
		String placeholderName = placeholder.getName();
		if (variableBindings.containsKey(placeholderName)) {
			constraints.push(constraintUnknowns.get(variableBindings.get(placeholderName)));
		} else {
			if (symbols.containsKey(placeholderName)) {
				// Could probably lazily handle binding here, but not elsewhere
				// (in useVariable(Reference)
				constraints.push(symbols.get(placeholderName));
			} else {
				useSymbol(placeholder);
				constraints.push(placeholder);
			}
		}
	}

	@Override
	public void bindVariable(String constraintUnknown, String constraintUnknownLocal, String placeholderName) {

		if (variableBindings.containsKey(placeholderName)) {
			String boundUnknown = variableBindings.get(placeholderName);
			if (!boundUnknown.equals(constraintUnknown)) {
				throw new IllegalStateException("Placeholder : [" + placeholderName + "] already bound to : ["
						+ variableBindings.get(placeholderName) + "], cannot bind it to : [" + constraintUnknown + "]");
			}
		}

		// Lazily create a new problem variable
		// variable name cannot simply be placeholder's name, because the same
		// expression can be considered multiple times, binding the same
		// placeolder to different constraint variables, example :
		//
		// while(i <= 500) ...
		//
		// makes two different constraint for the same placeholder :
		// i_prefinal <= 500 and i_final > 500
		if (!constraintUnknowns.containsKey(constraintUnknown)) {
			// TODO handle non integer variables
			ArithmeticVariableReference integerVariable = new ArithmeticVariableReference(constraintUnknown,
					constraintUnknownLocal, NumericType.INT);
			constraintUnknowns.put(constraintUnknown, integerVariable);
		}

		variableBindings.put(placeholderName, constraintUnknown);
	}

	@Override
	public void clearBindings() {
		variableBindings.clear();
		functionBindings.clear();
	}

	@Override
	public void constrain(CodeExpression expression) {
		expression.accept(this);
		model.add(constraints.pop());
	}

	@Override
	public Map<String, CodeExpression> solve(String minimizeVariableName)
			throws UnFeasibleException, CannotSolveException {
		System.out.println("------------");
		System.out.println("Initial Problem : ");
		System.out.println("------------");
		for (CodeExpression constraint : model) {
			System.out.println(constraint.toString());
		}
		System.out.println("------------");

		List<CodeExpression> initialFacts = new ArrayList<>();
		initialFacts.addAll(model);
		Map<String, CodeExpression> results = solveInequalitySystem(initialFacts);

		boolean completelySolved = simplifyWithSubstitution(results);

		if (results.containsKey(minimizeVariableName)) {
			if (ComparisonExpression.create(ComparisonOperator.GREATEREQUALTHAN, results.get(minimizeVariableName),
					new IntegerValueExpression(0)).equals(BooleanValueExpression.FALSE)) {
				throw new UnFeasibleException("number of steps : " + minimizeVariableName + " unfeasible : ["
						+ results.get(minimizeVariableName) + "]");
			}
		}

		System.out.println("------------");
		System.out.print("Result : ");
		if (completelySolved) {
			System.out.println("");
		} else {
			System.out.println("(INCOMPLETE)");
		}
		System.out.println("------------");
		for (String variableName : results.keySet()) {
			VariableReference variableReference = constraintUnknowns.get(variableName);
			System.out.println(variableReference.localName + " = " + results.get(variableName));
		}
		return results;
	}

	private Map<String, CodeExpression> solveInequalitySystem(List<CodeExpression> initialFacts)
			throws UnFeasibleException, CannotSolveException {
		Stack<List<CodeExpression>> equationSystems = new Stack<>();
		equationSystems.add(initialFacts);
		List<Map<String, CodeExpression>> systemsresults = new ArrayList<>();
		while (!equationSystems.isEmpty()) {
			List<CodeExpression> facts = equationSystems.pop();
			Map<String, CodeExpression> results = new LinkedHashMap<>();
			List<CodeExpression> evaluatedFacts;
			boolean somethingHasChanged;
			do {
				somethingHasChanged = false;
				evaluatedFacts = new ArrayList<>();
				evaluatedFacts.addAll(facts);
				for (CodeExpression constraint : facts) {
					if (constraint instanceof ComparisonExpression) {
						ComparisonExpression comparisonExpression = (ComparisonExpression) constraint;

						switch (comparisonExpression.operator) {
						case EQUAL: {
							VariableReference variableReference = null;
							CodeExpression variableValue = null;
							if (comparisonExpression.leftNormalizedInAVariable()) {
								variableReference = (VariableReference) comparisonExpression.leftSide;
								variableValue = comparisonExpression.rightSide;
							} else if (comparisonExpression.rightNormalizedInAVariable()) {
								variableReference = (VariableReference) comparisonExpression.rightSide;
								variableValue = comparisonExpression.leftSide;
							} else if (comparisonExpression.constant()) {
								System.out.println("Discarded fact : " + comparisonExpression);
								// TODO simply discarding this fact for now... should do something about it
								evaluatedFacts.remove(comparisonExpression);
								somethingHasChanged = true;
								break;
							} else {
								for (VariableReference variable : comparisonExpression.affectedVariables()) {
									variableReference = constraintUnknowns.get(variable.name);
									variableValue = PrologSimplifier.solveEquation(comparisonExpression, variable.name);
									if (variableValue != null) {
										variableValue = restorePlaceholders(variableValue);
										break;
									} else {
										// TODO simply discarding this fact for now... should do something about it
										System.out.println("Prolog solution : " + variableValue + " for : "
												+ comparisonExpression);
									}
								}
							}
							if (variableReference != null && variableValue != null) {
								updateFacts(evaluatedFacts, comparisonExpression, variableReference, variableValue,
										results);
								somethingHasChanged = true;
							}
							break;
						}
						case NOTEQUAL: {
							solveNotEqual(evaluatedFacts, comparisonExpression);
							somethingHasChanged = true;
							break;
						}
						case GREATERTHAN: {
							evaluatedFacts.remove(comparisonExpression);
							// Note : this is only valid for integers
							evaluatedFacts.add(ComparisonExpression.create(ComparisonOperator.GREATEREQUALTHAN,
									comparisonExpression.leftSide,
									BinaryIntegerExpression.create(BinaryArithmeticOperator.PLUS,
											comparisonExpression.rightSide, new IntegerValueExpression(1))));
							somethingHasChanged = true;
							break;
						}
						case LESSERTHAN: {
							evaluatedFacts.remove(comparisonExpression);
							// Note : this is only valid for integers
							evaluatedFacts.add(ComparisonExpression.create(ComparisonOperator.LESSEREQUALTHAN,
									comparisonExpression.leftSide,
									BinaryIntegerExpression.create(BinaryArithmeticOperator.MINUS,
											comparisonExpression.rightSide, new IntegerValueExpression(1))));
							somethingHasChanged = true;
							break;
						}
						case GREATEREQUALTHAN:
						case LESSEREQUALTHAN: {
							if (comparisonExpression.leftSolved()) {
								VariableReference variable = comparisonExpression.leftSide.affectedVariables().first();
								boolean otherFactsForThisVariable = false;
								for (CodeExpression otherFact : facts) {
									if (otherFact == comparisonExpression) {
										continue;
									}
									if (otherFact.affectedVariables().contains(variable)) {
										otherFactsForThisVariable = true;
										if (otherFact instanceof ComparisonExpression
												&& ((ComparisonExpression) otherFact).leftSolved()) {
											ComparisonExpression otherComparisonExpression = (ComparisonExpression) otherFact;
											if (otherComparisonExpression.operator
													.equals(comparisonExpression.operator)) {
												evaluatedFacts.remove(comparisonExpression);
												evaluatedFacts.remove(otherFact);

												// ex : i >= p && i >= q <=> i >= max(q,p)
												evaluatedFacts.add(ComparisonExpression.create(
														comparisonExpression.operator,
														comparisonExpression.leftSide,
														UnaryArithmeticExpression.create(
																comparisonExpression.operator.minimizingOperator(),
																BinaryExtremaExpression.create(
																		ExtremumOperator.MAX,
																		comparisonExpression.rightSide,
																		otherComparisonExpression.rightSide))));
												somethingHasChanged = true;
											} else if (otherComparisonExpression.operator
													.equals(ComparisonOperator.LESSEREQUALTHAN)
													|| otherComparisonExpression.operator
													.equals(ComparisonOperator.GREATEREQUALTHAN)) {
												evaluatedFacts.remove(comparisonExpression);
												evaluatedFacts.remove(otherFact);
												somethingHasChanged = true;
												CodeExpression lesserEqualThan;
												CodeExpression greaterEqualThan;
												if (comparisonExpression.operator
														.equals(ComparisonOperator.GREATEREQUALTHAN)) {
													greaterEqualThan = comparisonExpression.rightSide;
												} else {
													greaterEqualThan = otherComparisonExpression.rightSide;
												}
												if (comparisonExpression.operator
														.equals(ComparisonOperator.LESSEREQUALTHAN)) {
													lesserEqualThan = comparisonExpression.rightSide;
												} else {
													lesserEqualThan = otherComparisonExpression.rightSide;
												}
												BooleanExpression hasSolutionCondition = ComparisonExpression.create(
														ComparisonOperator.GREATEREQUALTHAN, lesserEqualThan,
														greaterEqualThan);
												if (hasSolutionCondition.equals(BooleanValueExpression.FALSE)) {
													throw new UnFeasibleException(comparisonExpression + " and "
															+ otherComparisonExpression + " are incompatible.");
												} else {
													// ex : i <= p && i >= q <=> true
													// nothing to do here already removed both facts
												}
											}
										}
									}
								}
								if (tominimize != null
										&& !otherFactsForThisVariable
										&& comparisonExpression.affectedVariables().size() == 1
										&& comparisonExpression.affectedVariables().contains(tominimize)) {
									evaluatedFacts.remove(comparisonExpression);
									evaluatedFacts.add(comparisonExpression.minimize(tominimize));
									somethingHasChanged = true;
								}
								continue;
							} else if (comparisonExpression.leftNormalizedInAVariable()) {
								continue;
							} else if (comparisonExpression.rightNormalizedInAVariable()) {
								evaluatedFacts.remove(comparisonExpression);
								evaluatedFacts.add(comparisonExpression.swapsides());
								somethingHasChanged = true;
								break;
							} else if (comparisonExpression.constant()) {
								evaluatedFacts.remove(comparisonExpression);
								somethingHasChanged = true;
								break;
							}

							// TODO handling polynomial case only, much easier, in other cases I should really extend
							// prolog code...
							CodeExpression polynomial = BinaryIntegerExpression.create(
									BinaryArithmeticOperator.MINUS, comparisonExpression.leftSide,
									comparisonExpression.rightSide);
							CodeExpression polynomialSimplified = null;
							for (VariableReference variable : comparisonExpression.affectedVariables()) {
								polynomialSimplified = PrologSimplifier.solvePolynomial(polynomial, variable.name);
								polynomialSimplified = restorePlaceholders(polynomialSimplified);
								if (polynomialSimplified != null && !polynomialSimplified.equals(polynomial)) {
									// evaluatedFacts.remove(comparisonExpression);
									// evaluatedFacts.add(ComparisonExpression.create(
									// comparisonExpression.operator,
									// polynomialSimplified,
									// new IntegerValueExpression(0)));
									// somethingHasChanged = true;
									break;
								}
							}
							// Ax + B ?
							if (polynomialSimplified instanceof BinaryIntegerExpression) {
								BinaryIntegerExpression binaryOuter = (BinaryIntegerExpression) polynomialSimplified;
								if (binaryOuter.rightSide.affectedVariables().isEmpty()) {
									IntegerValueExpression a = null;
									CodeExpression b = binaryOuter.rightSide;
									VariableReference x = null;
									if (binaryOuter.leftSide instanceof BinaryIntegerExpression) {
										// Ax ?
										BinaryIntegerExpression binaryInner = (BinaryIntegerExpression) binaryOuter.leftSide;
										if (binaryInner.leftSide instanceof IntegerValueExpression
												&& binaryInner.rightSide instanceof VariableReference
												&& binaryInner.operator.equals(BinaryArithmeticOperator.TIMES)) {
											a = (IntegerValueExpression) binaryInner.leftSide;
											x = (VariableReference) binaryInner.rightSide;
										}

									} else if (binaryOuter.leftSide instanceof VariableReference) {
										// x
										a = new IntegerValueExpression(1);
										x = (VariableReference) binaryOuter.leftSide;
									}
									if (a != null && b != null && x != null) {
										evaluatedFacts.remove(comparisonExpression);
										somethingHasChanged = true;
										if (a.value > 0) {
											// Ax+B > 0 => x > -B/A iff A > 0
											BooleanExpression constraintSolved = ComparisonExpression.create(
													comparisonExpression.operator, x,
													BinaryIntegerExpression.create(BinaryArithmeticOperator.DIV,
															MinusIntegerExpression.create(b), a));
											evaluatedFacts.add(constraintSolved);
										} else if (a.value < 0) {
											// Ax+B > 0 => x < -B/A iff A < 0
											BooleanExpression constraintSolved = ComparisonExpression.create(
													comparisonExpression.operator.swap(), x,
													BinaryIntegerExpression.create(BinaryArithmeticOperator.DIV,
															MinusIntegerExpression.create(b), a));
											evaluatedFacts.add(constraintSolved);
										}
									}

								}
							}
							break;
						}

						default:
							throw new UnsupportedOperationException(
									"Solving of comparison : [" + comparisonExpression + "] for operator : ["
											+ comparisonExpression.operator + "] has not yet been implemented.");
						}
					} else if (constraint instanceof BinaryBooleanExpression) {
						BinaryBooleanExpression booleanExpression = (BinaryBooleanExpression) constraint;
						switch (booleanExpression.operator) {
						case AND:
							evaluatedFacts.remove(constraint);
							somethingHasChanged = true;

							if (booleanExpression.leftSide instanceof BooleanExpression
									&& booleanExpression.rightSide instanceof ComparisonExpression) {
								ComparisonExpression comparison = (ComparisonExpression) booleanExpression.rightSide;
								if (ComparisonOperator.EQUAL.equals(comparison.operator)
										&& comparison.leftNormalizedInAVariable()) {
									VariableReference variable = comparison.leftSide.affectedVariables().first();
									CodeExpression value = null;
									if (!results.containsKey(variable.name)) {
										value = MultipleConditionedExpression.create(booleanExpression.leftSide,
												comparison.rightSide);
									} else {
										value = MultipleConditionedExpression.create(
												(MultipleConditionedExpression) results.get(variable.name),
												booleanExpression.leftSide, comparison.rightSide);
									}
									updateFacts(evaluatedFacts, constraint, variable, value, results);
									break;
								}
							}

							evaluatedFacts.add(booleanExpression.leftSide);
							evaluatedFacts.add(booleanExpression.rightSide);
							break;
						case OR:
							evaluatedFacts.remove(constraint);
							Map<String, CodeExpression> leftSolution = null;
							try {
								ArrayList<CodeExpression> leftFacts = new ArrayList<>(evaluatedFacts);
								leftFacts.add(booleanExpression.getLeftSide());
								leftSolution = solveInequalitySystem(leftFacts);
								for (String variableName : leftSolution.keySet()) {
									VariableReference variable = constraintUnknowns.get(variableName);
									CodeExpression variableValue = leftSolution.get(variableName);
									updateFacts(evaluatedFacts, constraint, variable, variableValue, results);
								}
							} catch (Exception e) {
								// pass
							}
							Map<String, CodeExpression> rightSolution = null;
							if (leftSolution == null) {
								try {
									ArrayList<CodeExpression> rightFacts = new ArrayList<>(evaluatedFacts);
									rightFacts.add(booleanExpression.getRightSide());
									rightSolution = solveInequalitySystem(rightFacts);
									for (String variableName : rightSolution.keySet()) {
										VariableReference variable = constraintUnknowns.get(variableName);
										CodeExpression variableValue = rightSolution.get(variableName);
										updateFacts(evaluatedFacts, constraint, variable, variableValue, results);
									}
								} catch (Exception e) {
									// pass
								}
							}

							somethingHasChanged = true;
							break;
						default:
							throw new UnsupportedOperationException(
									"Solving of composition : [" + booleanExpression + "] for operator : ["
											+ booleanExpression.operator + "] has not yet been implemented.");
						}
					} else if (constraint instanceof BooleanValueExpression) {
						BooleanValueExpression booleanExpression = (BooleanValueExpression) constraint;
						if (booleanExpression.equals(BooleanValueExpression.TRUE)) {
							evaluatedFacts.remove(constraint);
							somethingHasChanged = true;
						} else {
							throw new UnFeasibleException(constraint.toString());
						}
					} else {
						throw new UnsupportedOperationException(
								"Solving of : [" + constraint + "] has not yet been implemented.");
					}

					if (somethingHasChanged) {
						break;
					}
				}

				if (somethingHasChanged) {
					facts = new ArrayList<>();
					facts.addAll(evaluatedFacts);
					System.out.println("------------");
					System.out.println("Intermediate Results : ");
					System.out.println("------------");
					StringBuffer resultStringBuffer = resultsToString(results);
					System.out.println(resultStringBuffer.toString());
					System.out.println("------------");
					System.out.println("Intermediate Step : ");
					System.out.println("------------");
					for (CodeExpression constraint : facts) {
						System.out.println(constraint.toString());
					}
					System.out.println("------------");
				}
			} while (somethingHasChanged);

			if (!facts.isEmpty()) {
				throw new CannotSolveException("Problem could not be completely solved : [" + model
						+ "] initial facts : [" + facts + "], partial results : [" + resultsToString(results) + "]");
			}

			systemsresults.add(results);
		}

		if (systemsresults.size() == 1) {
			return systemsresults.get(0);
		} else {
			throw new UnsupportedOperationException("Not yet implemented");
		}
	}

	private void updateFacts(List<CodeExpression> evaluatedFacts, CodeExpression constraint,
			VariableReference variableReference, CodeExpression variableValue, Map<String, CodeExpression> results)
					throws UnFeasibleException {
		results.put(variableReference.name, variableValue);
		evaluatedFacts.remove(constraint);
		for (CodeExpression fact : new ArrayList<>(evaluatedFacts)) {
			if (!fact.affectedVariables().contains(variableReference)
					|| fact == constraint) {
				continue;
			}
			CodeExpression replacedFact = fact.replace(variableReference, variableValue);
			if (BooleanValueExpression.FALSE.equals(replacedFact)) {
				throw new UnFeasibleException("fact : " + fact + " is unfeasible.");
			}
			if (!BooleanValueExpression.TRUE.equals(replacedFact)) {
				evaluatedFacts.add(replacedFact);
			}
			evaluatedFacts.remove(fact);
		}
	}

	private StringBuffer resultsToString(Map<String, CodeExpression> results) {
		StringBuffer resultStringBuffer = new StringBuffer();
		for (String key : results.keySet()) {
			resultStringBuffer.append(constraintUnknowns.get(key) + ":=" + results.get(key) + "\n");
		}
		return resultStringBuffer;
	}

	private CodeExpression restorePlaceholders(CodeExpression variableValue) {
		for (VariableReference variableInValue : variableValue.affectedVariables()) {
			if (symbols.containsKey(variableInValue.name)) {
				variableValue = variableValue.replace(variableInValue, symbols.get(variableInValue.name));
			}
			if (constraintUnknowns.containsKey(variableInValue.name)) {
				variableValue = variableValue.replace(variableInValue, constraintUnknowns.get(variableInValue.name));
			}
		}
		return variableValue;
	}

	private static void solveNotEqual(List<CodeExpression> evaluatedFacts, ComparisonExpression comparisonExpression) {
		evaluatedFacts.remove(comparisonExpression);
		evaluatedFacts.add(BinaryBooleanExpression.create(BinaryBooleanOperator.OR,
				ComparisonExpression.create(ComparisonOperator.GREATERTHAN, comparisonExpression.leftSide,
						comparisonExpression.rightSide),
				ComparisonExpression.create(ComparisonOperator.LESSERTHAN, comparisonExpression.leftSide,
						comparisonExpression.rightSide)));
	}

	private boolean simplifyWithSubstitution(Map<String, CodeExpression> results) {
		boolean allVariablesReplaced;
		boolean somethingChanged;
		do {
			allVariablesReplaced = true;
			somethingChanged = false;
			for (String variableName : results.keySet()) {
				CodeExpression variableValue = results.get(variableName);
				for (VariableReference dependencyVariable : variableValue.affectedVariables()) {
					if (results.containsKey(dependencyVariable.name)) {
						CodeExpression newVariableValue = variableValue.replace(
								constraintUnknowns.get(dependencyVariable.name), results.get(dependencyVariable.name));
						variableValue = newVariableValue;
						results.put(variableName, newVariableValue);
						somethingChanged = true;
						continue;
					}
					// throw new IllegalArgumentException(
					// "Problem not completely solved : ["
					// + dependencyVariableName
					// + "] not in results : [" + results
					// + "]");
					continue;
					// TODO add a check it might be a parameter, otherwise
					// should fail as in commented code

				}
				SortedSet<VariableReference> affectedVariables = results.get(variableName).affectedVariables();
				if (!affectedVariables.isEmpty()) {
					allVariablesReplaced = false;
				}
			}
			if (!allVariablesReplaced && !somethingChanged) {
				// throw new IllegalStateException(
				// "Problem could not be completely solved : "
				// +
				// "cannot assign other variables and not all variables
				// assigned.");
				return false;
			}
		} while (!allVariablesReplaced && somethingChanged);
		return allVariablesReplaced;
	}

	@Override
	public void useVariable(VariableReference reference) {
		// Must have here both variablereferences (used by
		// infixexpressionvisitor)
		// and placeholder references (used by symbolicconstraintvisitor),
		// since there are many placeholders for a single variable (every time
		// it is assigned)
		String referenceName = reference.name;
		if (variableBindings.containsKey(referenceName)) {
			constraints.push(constraintUnknowns.get(variableBindings.get(referenceName)));
		} else {
			if (symbols.containsKey(referenceName)) {
				// Cannot lazily handle binding here : only have a reference,
				// not the real placeholder
				constraints.push(symbols.get(referenceName));
			} else {
				throw new IllegalArgumentException("No binding for variable : [" + referenceName + "]");
			}
		}
	}

	@Override
	public void useSymbol(SymbolicExpression symbol) {
		symbols.put(symbol.getName(), symbol);
		constraints.push(symbol);
	}

	@Override
	public void callFunction(String functionName, CodeExpression[] parameterValues) {
		if (!functionBindings.containsKey(functionName)) {
			throw new IllegalStateException("Function call placeholder : [" + functionName + "] not bound!");
		}
		constraints.push(constraintUnknowns.get(functionBindings.get(functionName)));
	}

	@Override
	public void bindFunction(String constraintUnknown, String constraintUnknownLocal, String placeholderName) {
		if (functionBindings.containsKey(placeholderName)) {
			throw new IllegalStateException("Placeholder : [" + placeholderName + "] already bound to : ["
					+ functionBindings.get(placeholderName) + "], cannot bind it to : [" + constraintUnknown + "]");
		}

		// Lazily create a new problem variable
		// variable name cannot simply be placeholder's name, because the same
		// expression can be considered multiple times, binding the same
		// placeolder to different constraint variables, example :
		//
		// if i <= 500 foo(i - 1) ...
		//
		// makes two different constraint for the same placeholder :
		// i_repeat <= 500 and i_final > 500
		if (!constraintUnknowns.containsKey(constraintUnknown)) {
			// TODO handle non integer variables
			ArithmeticVariableReference integerVariable = new ArithmeticVariableReference(constraintUnknown,
					constraintUnknownLocal, NumericType.INT);
			constraintUnknowns.put(constraintUnknown, integerVariable);
		}

		functionBindings.put(placeholderName, constraintUnknown);
	}

	@Override
	public void stopAt(CodeExpression expression) {
		constraints.push(expression);
	}

	@Override
	public void setMinimize(VariableReference variable) {
		tominimize = variable;
	}

}
