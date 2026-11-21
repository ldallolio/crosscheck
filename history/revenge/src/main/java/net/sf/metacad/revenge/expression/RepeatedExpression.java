package net.sf.metacad.revenge.expression;

import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

import net.sf.metacad.revenge.expression.arithmetic.BinaryArithmeticOperator;
import net.sf.metacad.revenge.expression.arithmetic.BinaryIntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;

public class RepeatedExpression extends ExpressionBase {

	private static final long serialVersionUID = -8971152340865023699L;

	public final IntegerExpression times;

	public final CodeExpression repeatedExpression;

	public final Map<String, CodeExpression> initialValues;

	private RepeatedExpression(CodeExpression originalExpression, IntegerExpression times,
			Map<String, CodeExpression> initialValues) {
		super();
		repeatedExpression = originalExpression;
		this.times = times;
		this.initialValues = initialValues;
	}

	public static CodeExpression create(CodeExpression originalExpression, IntegerExpression times,
			Map<String, CodeExpression> initialValues) {
		if (originalExpression instanceof ConstantExpression) {
			return originalExpression;
		}
		// if (originalExpression instanceof PlaceholderExpression) {
		// PlaceholderExpression placeholder = (PlaceholderExpression)
		// originalExpression;
		// return initialValues.get(placeholder.getLocalName());
		// }
		if (times instanceof IntegerValueExpression) {
			int timesValue = ((IntegerValueExpression) times).value;
			if (timesValue == 1) {
				return originalExpression;
			}
			if (timesValue == 0) {
				// use a MetaExpression ?
				throw new UnsupportedOperationException("not yet implemented");
			}
		}
		return new RepeatedExpression(originalExpression, times, initialValues);
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		TreeSet<VariableReference> treeSet = new TreeSet<>();
		treeSet.addAll(repeatedExpression.affectedVariables());
		treeSet.addAll(times.affectedVariables());
		// TODO : think about initial values : they could be filtered for
		// affectedvariablenames() in this.repeatedexpression and this.times
		return treeSet;
	}

	@Override
	public boolean isAbout(String variableName) {
		boolean about = repeatedExpression.isAbout(variableName) || times.isAbout(variableName);
		// TODO : think about initial values : you could filter for
		// affectedvariablenames() in this.repeatedexpression and this.times
		return about;
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		visitor.repeat(repeatedExpression, times, initialValues);
	}

	@Override
	public void repeat(IntegerExpression times2, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		IntegerExpression mult = (IntegerExpression) BinaryIntegerExpression.create(BinaryArithmeticOperator.TIMES,
				times, times2);
		visitor.repeat(repeatedExpression, mult, initialValues);
	}

	@Override
	public CodeType type() {
		return repeatedExpression.type();
	}

	@Override
	public CodeState evaluate(CodeState initialState) {
		// TODO Auto-generated method stub
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
	}

}