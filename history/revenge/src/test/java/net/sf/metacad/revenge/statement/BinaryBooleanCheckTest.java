package net.sf.metacad.revenge.statement;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonOperator;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.ProgramState;

import org.junit.Test;

public class BinaryBooleanCheckTest {

	@Test
	public void testEvaluate() throws Exception {
		BooleanExpression binaryBooleanStatement = ComparisonExpression.create(ComparisonOperator.EQUAL,
				new IntegerValueExpression(2), new IntegerValueExpression(3));
		CodeState programState = binaryBooleanStatement.evaluate(new ProgramState());
		assertNotNull(programState);
		assertEquals(BooleanValueExpression.FALSE, programState.getLeftValue());
	}

}
