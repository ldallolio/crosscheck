package net.sf.metacad.revenge.expression;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.apache.commons.lang.builder.ToStringBuilder;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;
import net.sf.metacad.revenge.type.MetaType;

public class MultipleValueExpression extends ExpressionBase {

	private static final long serialVersionUID = 3884468209636727059L;

	List<CodeExpression> values = new ArrayList<>();

	private MultipleValueExpression() {
	}

	public MultipleValueExpression(CodeExpression firstValue) {
		values.add(firstValue);
	}

	public MultipleValueExpression(List<CodeExpression> initialvalues) {
		values.addAll(initialvalues);
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		SortedSet<VariableReference> variableNames = new TreeSet<>();
		for (CodeExpression expression : values) {
			variableNames.addAll(expression.affectedVariables());
		}
		return variableNames;
	}

	@Override
	public boolean isAbout(String variableName) {
		for (CodeExpression expression : values) {
			if (expression.isAbout(variableName)) {
				return true;
			}
		}
		return false;
	}

	public void addValue(CodeExpression newValue) {
		values.add(newValue);
	}

	public CodeExpression getCurrentValue() {
		// get last
		return values.get(values.size() - 1);
	}

	public CodeExpression getInitialValue() {
		// get last
		return values.get(0);
	}

	public List<CodeExpression> getValues() {
		return values;
	}

	public void setValues(List<CodeExpression> variableValues) {
		values = variableValues;
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		// Not sure if this is completely correct
		visitor.follow(getCurrentValue());
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		visitor.follow(this);
	}

	@Override
	public String toString() {
		return new ToStringBuilder(this).append(values).toString();
	}

	@Override
	public CodeType type() {
		Set<CodeType> types = new HashSet<>();
		for (CodeType codeType : types) {
			types.add(codeType);
		}
		if (types.size() == 1) {
			return types.iterator().next();
		} else {
			return MetaType.MULTIPLE_TYPE;
		}
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		CodeState finalState = initialState;
		for (CodeExpression value : values) {
			finalState = value.evaluate(finalState);
		}
		return finalState;
	}

	@Override
	public CodeExpression replace(CodeExpression search, CodeExpression replace) {
		if (equals(search)) {
			return replace;
		} else {
			List<CodeExpression> replacedValues = new ArrayList<>();
			for (CodeExpression searchValue : values) {
				replacedValues.add(searchValue.replace(search, replace));
			}
			MultipleValueExpression replaced = new MultipleValueExpression();
			replaced.setValues(replacedValues);
			return replaced;
		}
	}

	@Override
	public boolean contains(CodeExpression search) {
		if (equals(search)) {
			return true;
		} else {
			boolean result = false;
			for (CodeExpression searchValue : values) {
				if (searchValue.contains(search)) {
					result = true;
					break;
				}
			}
			return result;
		}
	}

}
