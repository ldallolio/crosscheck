package net.sf.metacad.revenge.expression;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.Vector;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanOperator;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;

public class MultipleConditionedExpression extends ExpressionBase implements CodeExpression {

	private static final long serialVersionUID = -690933646083262449L;

	private final Map<BooleanExpression, CodeExpression> conditionedCodeExpressions = new LinkedHashMap<>();

	private CodeType type = null;

	private MultipleConditionedExpression() {
	}

	private MultipleConditionedExpression(CodeType type) {
		this.type = type;
	}

	@Override
	public boolean isAbout(String variableName) {
		throw new UnsupportedOperationException("not yet implemented");
		// return false;
	}

	static public CodeExpression create(BooleanExpression condition, CodeExpression expression) {
		return create(Collections.singletonMap(condition, expression));
	}

	static public CodeExpression create(Map<BooleanExpression, CodeExpression> conditionedExpressions) {

		if (conditionedExpressions == null) {
			throw new IllegalArgumentException("conditioned expressions not valid : [" + null + "]");
		}

		MultipleConditionedExpression multipleConditionedExpression = null;

		// Flattening complex types
		Map<BooleanExpression, CodeExpression> flattened = new LinkedHashMap<>();
		for (BooleanExpression condition : conditionedExpressions.keySet()) {
			CodeExpression expression = conditionedExpressions.get(condition);
			if (expression instanceof MultipleValueExpression) {
				MultipleValueExpression multipleExpression = (MultipleValueExpression) expression;
				for (CodeExpression value : multipleExpression.getValues()) {
					flattened.put(condition, value);
				}
				continue;
			}
			if (expression instanceof MultipleValuePlaceholder) {
				MultipleValuePlaceholder multiplePlaceholder = (MultipleValuePlaceholder) expression;
				if (multiplePlaceholder.value instanceof MultipleValueExpression) {
					MultipleValueExpression multipleExpression = (MultipleValueExpression) multiplePlaceholder.value;
					List<CodeExpression> newValues = new Vector<>(multipleExpression.values.size());
					for (CodeExpression value : multipleExpression.getValues()) {
						newValues.add(MultipleConditionedExpression.create(condition, value));
					}
					multipleExpression.values.clear();
					multipleExpression.values.addAll(newValues);
				}
			}
			flattened.put(condition, expression);
		}

		for (BooleanExpression condition : flattened.keySet()) {
			CodeExpression expression = flattened.get(condition);
			if (multipleConditionedExpression == null) {
				multipleConditionedExpression = new MultipleConditionedExpression(expression.type());
			} else {
				if (expression.type() != multipleConditionedExpression.type) {
					throw new IllegalArgumentException("incoherent types : [" + multipleConditionedExpression.type
							+ "], [" + expression.type() + "]");
				}
			}
			if (expression instanceof MultipleConditionedExpression) {
				MultipleConditionedExpression multipleExpression = (MultipleConditionedExpression) expression;
				for (BooleanExpression condition2 : multipleExpression.getConditions()) {
					BooleanExpression combinedCondition = BinaryBooleanExpression.create(BinaryBooleanOperator.AND,
							condition, condition2);
					if (BooleanValueExpression.FALSE.equals(combinedCondition)) {
						continue;
					}
					multipleConditionedExpression.conditionedCodeExpressions.put(combinedCondition,
							multipleExpression.getExpression(condition2));
				}
				continue;
			}
			if (BooleanValueExpression.FALSE.equals(condition)) {
				continue;
			}
			multipleConditionedExpression.conditionedCodeExpressions.put(condition,
					conditionedExpressions.get(condition));
		}

		if (multipleConditionedExpression.conditionedCodeExpressions.size() == 1) {
			BooleanExpression condition = multipleConditionedExpression.conditionedCodeExpressions.keySet().iterator()
					.next();
			if (BooleanValueExpression.TRUE.equals(condition)) {
				return multipleConditionedExpression.conditionedCodeExpressions.get(condition);
			}
		}

		return multipleConditionedExpression;
	}

	static public CodeExpression create(MultipleConditionedExpression multipleExpression, BooleanExpression condition,
			CodeExpression expression) {
		if (multipleExpression.getExpression(condition) != null) {
			throw new IllegalArgumentException(
					"Condition : [" + condition + "] already exists in expression : [" + multipleExpression + "]");
		}

		Map<BooleanExpression, CodeExpression> conditionedCodeExpressions = new LinkedHashMap<>();
		conditionedCodeExpressions.put(condition, expression);
		conditionedCodeExpressions.putAll(multipleExpression.conditionedCodeExpressions);
		return create(conditionedCodeExpressions);
	}

	public CodeExpression getExpression(BooleanExpression condition) {
		return conditionedCodeExpressions.get(condition);
	}

	public Set<BooleanExpression> getConditions() {
		return conditionedCodeExpressions.keySet();
	}

	public BooleanExpression getCompositeCondition() {
		BooleanExpression compositeExpression = null;
		for (BooleanExpression expression : conditionedCodeExpressions.keySet()) {
			if (compositeExpression != null) {
				compositeExpression = BinaryBooleanExpression.create(BinaryBooleanOperator.OR, compositeExpression,
						expression);
			} else {
				compositeExpression = expression;
			}
		}
		return compositeExpression;
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		SortedSet<VariableReference> multipleAffected = new TreeSet<>();
		for (BooleanExpression condition : conditionedCodeExpressions.keySet()) {
			CodeExpression conditionedExpression = conditionedCodeExpressions.get(condition);
			multipleAffected.addAll(condition.affectedVariables());
			multipleAffected.addAll(conditionedExpression.affectedVariables());
		}
		return multipleAffected;
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		for (CodeExpression condition : conditionedCodeExpressions.keySet()) {
			CodeExpression value = conditionedCodeExpressions.get(condition);
			// TODO check this one : no condition involved ??
			visitor.repeat(value, times, initialValues);
		}
	}

	@Override
	public CodeType type() {
		return type;
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		CodeState evaluatedState = initialState;
		Map<BooleanExpression, CodeExpression> evaluatedConditionedExpressions = new LinkedHashMap<>();
		for (BooleanExpression condition : conditionedCodeExpressions.keySet()) {
			evaluatedState = condition.evaluate(initialState);
			BooleanExpression conditionEvaluated = (BooleanExpression) evaluatedState.getLeftValue();
			evaluatedState = conditionedCodeExpressions.get(condition).evaluate(evaluatedState);
			CodeExpression valueEvaluated = evaluatedState.getLeftValue();
			evaluatedConditionedExpressions.put(conditionEvaluated, valueEvaluated);
		}
		evaluatedState.setLeftValue(MultipleConditionedExpression.create(evaluatedConditionedExpressions));
		return evaluatedState;
	}

	@Override
	public CodeExpression replace(CodeExpression search, CodeExpression replace) {
		Map<BooleanExpression, CodeExpression> replacedExpressions = new LinkedHashMap<>();
		for (BooleanExpression condition : conditionedCodeExpressions.keySet()) {
			CodeExpression conditionedExpression = conditionedCodeExpressions.get(condition);
			replacedExpressions.put((BooleanExpression) condition.replace(search, replace),
					conditionedExpression.replace(search, replace));
		}
		return MultipleConditionedExpression.create(replacedExpressions);
	}

}
