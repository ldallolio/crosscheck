package net.sf.metacad.revenge.constraint;

import net.sf.metacad.revenge.expression.arithmetic.IntegerPlaceholder;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonOperator;

import org.junit.Test;

public class ChocoConstraintVisitorTest {
	@Test
	public void testBinaryBooleanExpressionVisit() {
		ChocoConstraintVisitor visitor = new ChocoConstraintVisitor();
		BooleanExpression expression = ComparisonExpression.create(ComparisonOperator.EQUAL,
				new IntegerPlaceholder("a_0", "a_0", "a", new IntegerValueExpression(3),
						ChocoConstraintVisitorTest.class.getName()),
				new IntegerValueExpression(5));
		visitor.bindVariable("a_0", "a_0", "a_0");
		expression.accept(visitor);
	}
}
