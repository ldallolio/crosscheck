package net.sf.metacad.revenge.statement;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.expression.arithmetic.ArithmeticVariableReference;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.ProgramState;
import net.sf.metacad.revenge.state.StateTransition;
import net.sf.metacad.revenge.type.NumericType;

import org.junit.Test;

import bsh.JavaParser;

public class ReadVariableTest {

	@Test
	public void testEvaluate() throws Exception {
		StateTransition statement = JavaParser.parse("int var1 = 42;");
		CodeState initialState = statement.evaluate(new ProgramState());
		VariableReference readvarinstr = new ArithmeticVariableReference("var1", NumericType.INT);
		CodeState finalState = readvarinstr.evaluate(initialState);
		assertNotNull(finalState);
		assertEquals(42, ((IntegerValueExpression) finalState.getLeftValue()).value);
		assertEquals(42, ((IntegerValueExpression) finalState.variableValue("var1")).value);
	}

}
