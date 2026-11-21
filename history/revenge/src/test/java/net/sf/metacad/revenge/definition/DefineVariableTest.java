package net.sf.metacad.revenge.definition;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.ProgramState;
import net.sf.metacad.revenge.state.StateTransition;

import org.junit.Test;

import bsh.JavaParser;

public class DefineVariableTest {

	@Test
	public void testEvaluate() throws Exception {
		StateTransition statement = JavaParser.parse("int var1 = 42;");
		CodeState finalState = statement.evaluate(new ProgramState());
		assertNotNull(finalState);
		assertEquals(new IntegerValueExpression(42), finalState.getLeftValue());
		assertEquals(new IntegerValueExpression(42), finalState.variableValue("var1"));
	}

}
