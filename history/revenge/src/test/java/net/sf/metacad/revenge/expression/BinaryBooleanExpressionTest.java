package net.sf.metacad.revenge.expression;

import static org.junit.Assert.assertTrue;
import net.sf.metacad.revenge.expression.arithmetic.IntegerPlaceholder;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanOperator;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonOperator;

import org.junit.Test;

public class BinaryBooleanExpressionTest {

	@Test
	public void testNotSimplified() {
		IntegerPlaceholder n0 = new IntegerPlaceholder("n_0");
		BooleanExpression c1 = ComparisonExpression.create(ComparisonOperator.EQUAL, n0, new IntegerValueExpression(0));
		BooleanExpression c2 = ComparisonExpression.create(ComparisonOperator.NOTEQUAL, n0,
				new IntegerValueExpression(0));
		BooleanExpression c1andc2 = BinaryBooleanExpression.create(BinaryBooleanOperator.AND, c1, c2);
		assertTrue(c1andc2.equals(BooleanValueExpression.FALSE));
	}

}
