package net.sf.metacad.revenge.state;

import java.io.Serializable;

import org.apache.commons.lang.SerializationUtils;
import org.apache.commons.lang.builder.ToStringBuilder;

@SuppressWarnings("serial")
abstract class AbstractState implements Serializable, CodeState {

	protected String creatorDescription = null;
	protected WrappingState wrappingState = null;

	public AbstractState() {
		super();
	}

	@Override
	public final String toString() {
		return ToStringBuilder.reflectionToString(this);
	}

	@Override
	protected final Object clone() throws CloneNotSupportedException {
		return SerializationUtils.clone(this);
	}

	@Override
	public final CodeState cloneState() {
		try {
			return (CodeState) this.clone();
		} catch (CloneNotSupportedException e) {
			throw new IllegalStateException(e);
		}
	}

	@Override
	public final void setCreatorDescription(String creatorDescription) {
		this.creatorDescription = creatorDescription;
	}

	@Override
	public void setWrappingState(WrappingState wrappingState) {
		this.wrappingState = wrappingState;
	}

}