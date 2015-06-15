package za.ac.sun.cs.green.expr;

public class BitVectorVariable extends Variable{
	
	/*
	 * Unlike the previous ones, this is just an alias for actual operations
	 */

	private final Integer lowerBound;

	private final Integer upperBound;

	public BitVectorVariable(String name, Expression alias, Integer lowerBound, Integer upperBound) {
		super(name);
		this.lowerBound = lowerBound;
		this.upperBound = upperBound;
	}

	public Integer getLowerBound() {
		return lowerBound;
	}

	public Integer getUpperBound() {
		return upperBound;
	}
	
	@Override
	public int hashCode() {
		return this.getName().hashCode();
	}

	@Override
	public String toString() {
		return this.getName();
	}

	@Override
	public void accept(Visitor visitor) throws VisitorException {
		visitor.preVisit(this);
		visitor.postVisit(this);
	}

	@Override
	public boolean equals(Object object) {
		if (object instanceof IntVariable) {
			IntVariable variable = (IntVariable) object;
			return getName().equals(variable.getName());
		} else {
			return false;
		}
	}
}
