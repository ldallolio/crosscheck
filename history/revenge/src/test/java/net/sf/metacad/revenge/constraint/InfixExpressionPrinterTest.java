package net.sf.metacad.revenge.constraint;

import static org.junit.Assert.assertNotNull;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.state.CodeState;

import org.junit.Test;

import bsh.JavaParser;

public class InfixExpressionPrinterTest {

	@Test
	public void test() throws Exception {
		CodeState initialState = JavaParser.evaluate("int a;");
		CodeExpression equation = (CodeExpression) JavaParser.parse("a==3*9/6", initialState);
		InfixExpressionPrinter infixExpressionPrinter = new InfixExpressionPrinter();
		String infixExpression = infixExpressionPrinter.convert(equation);
		assertNotNull(infixExpression);
	}

}
