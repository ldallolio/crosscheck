package net.sf.metacad.revenge.constraint;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.UUID;

import org.apache.commons.lang.StringUtils;

import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.MultipleConditionedExpression;
import net.sf.metacad.revenge.expression.MultipleValueExpression;
import net.sf.metacad.revenge.expression.PlaceholderExpression;
import net.sf.metacad.revenge.expression.RecursiveCallExpression;
import net.sf.metacad.revenge.expression.RepeatedExpression;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.expression.arithmetic.BinaryArithmeticOperator;
import net.sf.metacad.revenge.expression.arithmetic.BinaryIntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerPlaceholder;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanOperator;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonOperator;
import net.sf.metacad.revenge.expression.logic.NotExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.PlaceholderState;
import net.sf.metacad.revenge.state.RecursionRecordState;

public class RepeatProjector {

	public static final String RETURN_RECURSION = "return_recursion";
	private static final String INITIAL_SUFFIX = "_initial";
	private static final String REPEAT_SUFFIX = "_repeat";
	private static final String FINAL_SUFFIX = "_final";

	public static Map<String, CodeExpression> solveRepeatProblem(CodeState repeatClauseState, CodeState initialState,
			BooleanExpression repeatClauseCondition, ConstraintSolver visitor, CodeExpression returnExpression,
			RecursionRecordState recursionState) throws UnFeasibleException, CannotSolveException {

		if (repeatClauseCondition == null) {
			throw new IllegalArgumentException("Clause not valid : [" + repeatClauseCondition + "]");
		}

		// Setting up variable extrapolation
		//
		// Simple example : int x, i = 0; while(i < 5) {x = i;i++;}
		//
		// placeholders : i_0 == 0, x_0 == i_0, i_1 == i_0 + 1
		//
		// Complex example : int i = x = y = 0; while(i < 5) {i++;x = i;i++;y =
		// i;y++}
		//
		// I will try to just do variable replacement for this part
		//
		// Should I consider break condition affected variables?
		//
		// Example : int x, i = 0; while(i < 15) {if (x > 6) break; x++; i++;}
		//
		// Should I consider return condition affected variables?
		// Example : int x, i = 0; while(i < 15) {if (x > 6) return "hi"; x++;
		// i++;}

		// Defining placeholder variables

		// Setting each suffix separately one from the other
		String numStepsVariableName = "num_steps_in_cycle_"
				+ StringUtils.replaceChars(UUID.randomUUID().toString(), '-', '_');
		String returnVariableName = "return_stop_" + StringUtils.replaceChars(UUID.randomUUID().toString(), '-', '_');
		IntegerPlaceholder return_stop = new IntegerPlaceholder(returnVariableName, "return_stop", returnVariableName,
				new IntegerValueExpression(0), RepeatProjector.class.getName());
		String recursionVariableName = RETURN_RECURSION + "_"
				+ StringUtils.replaceChars(UUID.randomUUID().toString(), '-', '_');
		IntegerPlaceholder recursion = new IntegerPlaceholder(recursionVariableName, "recursion", recursionVariableName,
				new IntegerValueExpression(0), RepeatProjector.class.getName());

		CodeExpression stopRecursionExpression = null;
		CodeExpression backwardRecursionExpression = null;
		if (returnExpression != null) {
			stopRecursionExpression = MultipleConditionedExpression.create(NotExpression.create(repeatClauseCondition),
					returnExpression);
			backwardRecursionExpression = MultipleConditionedExpression.create(repeatClauseCondition, returnExpression);
		}

		ConstraintSolver visitorClause = new SymbolicConstraintVisitor();
		addSuffixConstraints(numStepsVariableName, return_stop, recursion, repeatClauseState, visitorClause,
				initialState, repeatClauseCondition, stopRecursionExpression, backwardRecursionExpression,
				recursionState, new String[] { INITIAL_SUFFIX }, null);

		// Solving the problem for the clause only to see if it is unfeasible
		// meaning the cycle is never entered
		// Not really interested in solution anyway
		try {
			System.out.println("C L A U S E    S O L U T I O N");
			visitorClause.solve(numStepsVariableName);
		} catch (UnFeasibleException e) {
			// The while is never entered
			return new LinkedHashMap<>();
		}

		System.out.println("F I R S T    C Y C L E    S O L U T I O N");
		// Solving without initial conditions to obtain symbolic expressions for the first cycle
		ConstraintSolver visitor0 = new SymbolicConstraintVisitor();
		addSuffixConstraints(numStepsVariableName, return_stop, recursion, repeatClauseState, visitor0, initialState,
				repeatClauseCondition, stopRecursionExpression, backwardRecursionExpression, recursionState,
				new String[] { REPEAT_SUFFIX, FINAL_SUFFIX }, null);

		// Adding constraints between suffixes (crossing the binding)
		addCrossSuffixConstraints(initialState, visitor0, recursionState, null);

		// TODO this could be avoided by passing a placeholderstate that could
		// do resolveVariable()
		Map<String, PlaceholderExpression> placeholderByGlobal = new LinkedHashMap<>();
		for (String variableName : initialState.variableNames()) {
			// Set the variable initial value (before entering the loop)
			MultipleValueExpression multipleValue = (MultipleValueExpression) initialState.variableValue(variableName);
			for (CodeExpression expression : multipleValue.getValues()) {
				PlaceholderExpression placeholder = (PlaceholderExpression) expression;
				placeholderByGlobal.put(placeholder.getName(), placeholder);
			}
		}

		// Solving the problem for the first cycle without initial data to
		// obtain cycle formulas
		Map<String, CodeExpression> solution0 = visitor0.solve(numStepsVariableName);

		Map<String, CodeExpression> firstCycleValues = new LinkedHashMap<>();
		for (String constraintVariableName : solution0.keySet()) {
			if (constraintVariableName.endsWith(FINAL_SUFFIX)) {
				String placeholderName = StringUtils.removeEnd(constraintVariableName, FINAL_SUFFIX);
				CodeExpression value = solution0.get(constraintVariableName);
				PlaceholderExpression placeholder = placeholderByGlobal.get(placeholderName);
				for (VariableReference expressionVariable : value.affectedVariables()) {
					String placeholderExpressionName = StringUtils.removeEnd(expressionVariable.name, REPEAT_SUFFIX);
					PlaceholderExpression placeholder2 = placeholderByGlobal.get(placeholderExpressionName);
					value = value.replace(expressionVariable, placeholder2.reference());
				}
				// Setting initial values for other placeholders
				firstCycleValues.put(placeholder.getLocalName(), value);
			}
		}

		System.out.println("R E P E A T    S O L U T I O N");
		addSuffixConstraints(numStepsVariableName, return_stop, recursion, repeatClauseState, visitor, initialState,
				repeatClauseCondition, stopRecursionExpression, backwardRecursionExpression, recursionState,
				new String[] { INITIAL_SUFFIX, REPEAT_SUFFIX, FINAL_SUFFIX }, firstCycleValues);

		// Adding constraints between suffixes (crossing the binding)
		addCrossSuffixConstraints(initialState, visitor, recursionState, firstCycleValues);

		Map<String, CodeExpression> solution = visitor.solve(numStepsVariableName);

		Map<String, CodeExpression> finalExpressions = makeFinalValues(solution, initialState);
		if (returnExpression != null) {
			finalExpressions.put("return_stop", solution.get(returnVariableName));
			finalExpressions.put(RETURN_RECURSION, solution.get(recursionVariableName));
		}

		return finalExpressions;
	}

	private static Map<String, CodeExpression> makeFinalValues(Map<String, CodeExpression> solution,
			CodeState initialState) {
		Map<String, CodeExpression> finalExpressions = new LinkedHashMap<>();
		// TODO this could be avoided by passing a placeholderstate that could
		// be resolveVariable()
		Map<String, String> variableByPlaceholder = new LinkedHashMap<>();
		for (String variableName : initialState.variableNames()) {
			MultipleValueExpression multipleValue = (MultipleValueExpression) initialState.variableValue(variableName);
			for (CodeExpression expression : multipleValue.getValues()) {
				PlaceholderExpression placeholder = (PlaceholderExpression) expression;
				variableByPlaceholder.put(placeholder.getName(), variableName);
			}
		}
		Map<String, String> finalPlaceholderByVariable = new LinkedHashMap<>();
		for (String constraintVariableName : solution.keySet()) {
			if (constraintVariableName.endsWith(REPEAT_SUFFIX)) {
				String placeholderName = StringUtils.removeEnd(constraintVariableName, REPEAT_SUFFIX);
				String variableName = variableByPlaceholder.get(placeholderName);
				// Sometimes a variable will not be in while clause (so it will
				// have no final constraint variable), so I am taking repeat
				// variables too, example :
				// int i = 0;int x;
				// while (i != 1) {x = i; i = i + 1};
				// here "x" variable is global but not in while clause
				if (!solution.containsKey(placeholderName + FINAL_SUFFIX)
						&& !finalPlaceholderByVariable.containsKey(variableName)) {
					finalExpressions.put(placeholderName, solution.get(constraintVariableName));
				}
			}

			if (constraintVariableName.endsWith(FINAL_SUFFIX)) {
				String placeholderName = StringUtils.removeEnd(constraintVariableName, FINAL_SUFFIX);
				finalExpressions.put(placeholderName, solution.get(constraintVariableName));
				String variableName = variableByPlaceholder.get(placeholderName);
				finalPlaceholderByVariable.put(variableName, placeholderName);
			}

		}

		return finalExpressions;
	}

	private static void addCrossSuffixConstraints(CodeState innerState, ConstraintSolver visitor,
			RecursionRecordState recursionState, Map<String, CodeExpression> firstCycleValues) {

		for (String variableName : innerState.variableNames()) {
			MultipleValueExpression multipleValue = (MultipleValueExpression) innerState.variableValue(variableName);
			PlaceholderExpression firstPlaceholder = (PlaceholderExpression) multipleValue.getInitialValue();
			PlaceholderExpression lastPlaceholder = (PlaceholderExpression) multipleValue.getCurrentValue();

			// Constraining repeated variables with prefinal, if different
			if (!lastPlaceholder.equals(firstPlaceholder) && recursionState == null) {

				visitor.clearBindings();

				visitor.bindVariable(lastPlaceholder.getName() + INITIAL_SUFFIX,
						lastPlaceholder.getLocalName() + INITIAL_SUFFIX, lastPlaceholder.getName());
				visitor.bindVariable(firstPlaceholder.getName() + INITIAL_SUFFIX,
						firstPlaceholder.getLocalName() + INITIAL_SUFFIX, firstPlaceholder.getName());
				visitor.constrain(
						ComparisonExpression.create(ComparisonOperator.EQUAL, lastPlaceholder, firstPlaceholder));

				visitor.clearBindings();

				visitor.bindVariable(lastPlaceholder.getName() + INITIAL_SUFFIX,
						lastPlaceholder.getLocalName() + INITIAL_SUFFIX, lastPlaceholder.getName());
				visitor.bindVariable(firstPlaceholder.getName() + REPEAT_SUFFIX,
						firstPlaceholder.getLocalName() + REPEAT_SUFFIX, firstPlaceholder.getName());
				visitor.constrain(
						ComparisonExpression.create(ComparisonOperator.EQUAL, lastPlaceholder, firstPlaceholder));

				visitor.clearBindings();

				visitor.bindVariable(lastPlaceholder.getName() + REPEAT_SUFFIX,
						lastPlaceholder.getLocalName() + REPEAT_SUFFIX, lastPlaceholder.getName());

				visitor.bindVariable(firstPlaceholder.getName() + FINAL_SUFFIX,
						firstPlaceholder.getLocalName() + FINAL_SUFFIX, firstPlaceholder.getName());
				visitor.constrain(
						ComparisonExpression.create(ComparisonOperator.EQUAL, lastPlaceholder, firstPlaceholder));

			}

			visitor.clearBindings();

		}

		if (recursionState != null) {
			for (String placeholderName : recursionState.functionPlaceholderByName.keySet()) {
				RecursiveCallExpression callExpression = recursionState.functionPlaceholderByName.get(placeholderName);
				int position = 0;
				for (VariableDefinition parameter : callExpression.functionDefinition.parameterDefinitions) {
					MultipleValueExpression multipleValue = (MultipleValueExpression) innerState
							.variableValue(parameter.name);
					PlaceholderExpression firstPlaceholder = (PlaceholderExpression) multipleValue.getInitialValue();
					PlaceholderExpression parameterValue = (PlaceholderExpression) callExpression.assignedParameterValues
							.get(position);
					visitor.bindVariable(parameterValue.getName() + REPEAT_SUFFIX,
							parameterValue.getLocalName() + REPEAT_SUFFIX, parameterValue.getName());
					visitor.bindVariable(firstPlaceholder.getName() + FINAL_SUFFIX,
							firstPlaceholder.getLocalName() + FINAL_SUFFIX, firstPlaceholder.getName());
					visitor.constrain(
							ComparisonExpression.create(ComparisonOperator.EQUAL, parameterValue, firstPlaceholder));
					position++;
				}
			}
		}

	}

	protected static void addSuffixConstraints(String numStepsVariableName, IntegerPlaceholder return_stop,
			IntegerPlaceholder recursion, CodeState repeatClauseState, ConstraintSolver visitor, CodeState initialState,
			BooleanExpression repeatClauseCondition, CodeExpression stopRecursionExpression,
			CodeExpression backwardRecursionExpression, RecursionRecordState recursionState, String[] suffixes,
			Map<String, CodeExpression> firstCycleValues) {

		IntegerPlaceholder steps = new IntegerPlaceholder(numStepsVariableName, "steps", numStepsVariableName,
				new IntegerValueExpression(0), RepeatProjector.class.getName());

		// TODO : handle continue and return statements
		for (String suffix : suffixes) {

			// Cannot add constraints until all placeholder variables are bound,
			// so I bind them all at the beginning of each suffix
			// Example : int x,i = 0; while(++i <= 50) { x = i++;i = x++;}
			bindPlaceholderConstraintVariables(repeatClauseState, initialState, recursionState, visitor, suffix);
			visitor.bindVariable(numStepsVariableName, "steps", steps.name);

			if (REPEAT_SUFFIX.equals(suffix)) {
				if (firstCycleValues == null) {
					// Only doing one cycle for initial resolution
					visitor.constrain(ComparisonExpression.create(ComparisonOperator.EQUAL, steps.reference(),
							new IntegerValueExpression(1)));
				} else {
					// TODO : remove this, information already provided during solve() call, now it is duplicated!
					visitor.setMinimize(steps.reference());
				}
			}
			visitor.bindVariable(return_stop.name, "stop_return", return_stop.name);
			visitor.bindVariable(recursion.name, "recursion", recursion.name);

			// All constraint variables for this suffix are bound now, so I
			// can constrain expressions.
			addPlaceholderConstraints(repeatClauseState, initialState, recursionState, visitor, suffix, steps,
					repeatClauseCondition, return_stop, firstCycleValues);

			if (FINAL_SUFFIX.equals(suffix) && stopRecursionExpression != null) {
				visitor.bindFunction("stop_return_final", "stop_return_final", return_stop.name);
				visitor.constrain(ComparisonExpression.create(ComparisonOperator.EQUAL, return_stop.reference(),
						stopRecursionExpression));
			}

			// Cycle enter condition
			if (INITIAL_SUFFIX.equals(suffix)) {
				visitor.constrain(repeatClauseCondition);
			}

			// Cycle stay condition
			if (REPEAT_SUFFIX.equals(suffix) && firstCycleValues != null) {
				visitor.constrain(repeatClauseCondition);
			}

			// Cycle exit condition
			if (FINAL_SUFFIX.equals(suffix) && firstCycleValues != null) {
				BooleanExpression repeatExitCondition = NotExpression.create(repeatClauseCondition);
				visitor.constrain(repeatExitCondition);
			}

			if (REPEAT_SUFFIX.equals(suffix) && backwardRecursionExpression != null) {
				// TODO : think about recursion backward expression initial
				// value, what is it?
				visitor.constrain(
						ComparisonExpression.create(ComparisonOperator.EQUAL, recursion.reference(), RepeatedExpression
								.create(backwardRecursionExpression, steps, null /* TODO recursion here ??? */)));
			}

			visitor.clearBindings();
		}
	}

	private static void addPlaceholderConstraints(CodeState repeatClauseState, CodeState innerState,
			RecursionRecordState recursionState, ConstraintSolver visitor, String suffix, IntegerPlaceholder steps,
			BooleanExpression repeatClauseCondition, IntegerPlaceholder return_stop,
			Map<String, CodeExpression> firstCycleValues) {

		BooleanExpression repeatExitCondition = NotExpression.create(repeatClauseCondition);

		CodeState state = null;
		if (FINAL_SUFFIX.equals(suffix)) {
			state = repeatClauseState;
		} else {
			state = innerState;
		}

		// Add placeholder constraints
		for (String variableName : state.variableNames()) {

			CodeExpression variableValue = state.variableValue(variableName);

			if (!(variableValue instanceof MultipleValueExpression)) {
				// Remember that while clause state is used here as well (in
				// final
				// constraints), with a
				// different set of variables, example :
				// int i = 0;int x;
				// while (i != 1) {x = i; i = i + 1};
				// in the example above, "x" variable is taken from while clause
				// state during final constraints and
				// is not initialized
				// Example (look at j which will stay constant in while cycle) :
				// int i = 7; int j = 9; while (i != 13) i = i + 1;
				// placeholder produced by some outer loops's state (that is
				// still
				// placeholding, this is why it is not a
				// multiplevalueexpression).
				// Will treat it like a parameter, or unknown constant
				continue;
			}
			MultipleValueExpression multipleValue = (MultipleValueExpression) variableValue;
			List<CodeExpression> placeholders = multipleValue.getValues();
			boolean first = true;

			for (CodeExpression codeExpression : placeholders) {
				PlaceholderExpression placeholder = (PlaceholderExpression) codeExpression;

				// Example : int i = 7; while (i != 13) i = i + 2;
				// placeholder i_0 = 7 (that is, first variable for i)
				// placeholder i_1 = i_0 + 2 (that is, second variable for i
				// after assignment)
				// constraint variable : i_0_repeat = 7 = 7 = ... = 7 (that
				// is,
				// first variable for i never changed by the cycle)
				// constraint variable : i_1_repeat = 7 + 2 + ... + 2 = 7 +
				// n *
				// 2 (that is, second variable for i changed by the cycle)

				if (INITIAL_SUFFIX.equals(suffix) && first) {
					visitor.constrain(ComparisonExpression.create(ComparisonOperator.EQUAL, placeholder.reference(),
							placeholder.getValue()));
				}

				if (REPEAT_SUFFIX.equals(suffix) && (!first || placeholders.size() == 1)) {
					CodeExpression loopingPlaceholderValue = placeholder.getValue();

					// Need to make recursion explicit
					// Example : int i = 7; while (i != 13) { i = i + 2; }
					// i_1 = i_0 + 2 must become i_1 = repeat(i_1 + 2, times, i=7)
					// TODO : should be done using a separate equation ?
					// TODO make all this simpler by using placeholderstate.

					if (firstCycleValues != null) {

						for (String aVariableName : state.variableNames()) {

							CodeExpression aVariableValue = state.variableValue(aVariableName);

							if (!(aVariableValue instanceof MultipleValueExpression)) {
								continue;
							}
							MultipleValueExpression aMultipleValue = (MultipleValueExpression) aVariableValue;
							List<CodeExpression> aPlaceholders = aMultipleValue.getValues();
							if (aPlaceholders.size() == 1) {
								continue;
							}

							PlaceholderExpression firstPlaceholder = (PlaceholderExpression) aPlaceholders.get(0);
							PlaceholderExpression lastPlaceholder = (PlaceholderExpression) aPlaceholders
									.get(aPlaceholders.size() - 1);
							CodeExpression nextcycleInitialValue = firstCycleValues
									.get(firstPlaceholder.getLocalName());

							IntegerExpression stepsMinus1 = (IntegerExpression) BinaryIntegerExpression
									.create(BinaryArithmeticOperator.MINUS, steps, new IntegerValueExpression(1));
							loopingPlaceholderValue = loopingPlaceholderValue.replace(firstPlaceholder,
									RepeatedExpression.create(nextcycleInitialValue, stepsMinus1, firstCycleValues));
						}
					}

					visitor.constrain(BinaryBooleanExpression.create(BinaryBooleanOperator.AND, repeatClauseCondition,
							ComparisonExpression
							.create(ComparisonOperator.EQUAL, placeholder.reference(), loopingPlaceholderValue)));
				}

				if (FINAL_SUFFIX.equals(suffix) && !first) {
					// Final variables are not "repeated"
					visitor.constrain(BinaryBooleanExpression.create(BinaryBooleanOperator.AND, repeatExitCondition,
							ComparisonExpression.create(ComparisonOperator.EQUAL, placeholder,
									placeholder.getValue())));
				}

				first = false;
			}
		}

		if (recursionState != null) {
			for (String placeholderName : recursionState.functionPlaceholderByName.keySet()) {
				RecursiveCallExpression callExpression = recursionState.functionPlaceholderByName.get(placeholderName);
				if (REPEAT_SUFFIX.equals(suffix)) {
					visitor.constrain(ComparisonExpression.create(ComparisonOperator.EQUAL, return_stop.reference(),
							callExpression));
				}
			}
		}

	}

	protected static void bindPlaceholderConstraintVariables(CodeState repeatClauseState, CodeState innerState,
			RecursionRecordState recursionState, ConstraintSolver visitor, String suffix) {

		CodeState state = null;
		if (FINAL_SUFFIX.equals(suffix)) {
			state = repeatClauseState;
		} else {
			state = innerState;
		}

		// Bind constraint variables with placeholders
		// It cannot be done lazily in constraintvisitor because of placeholder
		// references that would arrive sooner than their placeholders
		for (String variableName : state.variableNames()) {

			CodeExpression variableValue = state.variableValue(variableName);

			if (!(variableValue instanceof MultipleValueExpression)) {
				// Remember that while clause state is used here as well (in
				// final
				// constraints), with a
				// different set of variables, example :
				// int i = 0;int x;
				// while (i != 1) {x = i; i = i + 1};
				// in the example above, "x" variable is taken from while clause
				// state during final constraints and
				// is not initialized
				// example (look at j which will stay constant in while cycle) :
				// int i = 7; int j = 9; while (i != 13) i = i + 1;
				// placeholder produced by some outer loops's state (that is
				// still
				// placeholding, this is why it is not a
				// multiplevalueexpression).
				// Will treat it like a parameter, or unknown constant
				continue;
			}
			MultipleValueExpression multipleValue = (MultipleValueExpression) variableValue;
			List<CodeExpression> placeholders = multipleValue.getValues();
			boolean first = true;
			for (CodeExpression codeExpression : placeholders) {
				PlaceholderExpression placeholder = (PlaceholderExpression) codeExpression;

				// Placeholder names must be made unique in different
				// cycles, so
				// I add a suffix here
				String constraintVariableName = null;
				String placeholderLocalName = null;

				constraintVariableName = placeholder.getName() + suffix;
				placeholderLocalName = placeholder.getLocalName() + suffix;

				// Example : placeholder i_0 bound to constraint variable
				// i_0_repeat
				visitor.bindVariable(constraintVariableName, placeholderLocalName, placeholder.getName());

				first = false;
			}
		}

		if (recursionState != null) {
			for (String placeholderName : recursionState.functionPlaceholderByName.keySet()) {
				RecursiveCallExpression callExpression = recursionState.functionPlaceholderByName.get(placeholderName);
				String constraintVariableName = callExpression.placeholderName + suffix;
				visitor.bindFunction(constraintVariableName, callExpression.placeholderLocalName + suffix,
						callExpression.placeholderName);
			}
		}
	}

	public static Map<String, CodeExpression> resolvingFinalVariables(PlaceholderState initialState,
			Map<String, CodeExpression> clauseFinalVariables) {
		Map<String, CodeExpression> variables = new LinkedHashMap<>();
		for (String placeholderName : clauseFinalVariables.keySet()) {

			String variableName = initialState.resolvePlaceholder(placeholderName);

			// Understand which variables are final :
			// int i = 0;while(i++ <= 10) {i+=2;}
			// final value for i is 13
			if (initialState.isGloballyDefined(variableName)) {
				variables.put(variableName, clauseFinalVariables.get(placeholderName));
			}

		}
		return variables;
	}
}
