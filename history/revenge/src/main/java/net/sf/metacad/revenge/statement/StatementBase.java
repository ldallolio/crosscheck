package net.sf.metacad.revenge.statement;

import org.apache.commons.lang.builder.ToStringBuilder;

public abstract class StatementBase implements CodeStatement {

	private static final long serialVersionUID = -5011215799254835929L;

	@Override
	public String toString() {
		return ToStringBuilder.reflectionToString(this);
	}

}