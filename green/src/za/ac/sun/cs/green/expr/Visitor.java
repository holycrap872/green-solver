package za.ac.sun.cs.green.expr;

public abstract class Visitor {

	public void preVisit(Constant constant) throws VisitorException {
		preVisit((Expression) constant);
	}

	public void preVisit(Expression expression) throws VisitorException {
	}

	public void preVisit(IntConstant intConstant) throws VisitorException {
		preVisit((Constant) intConstant);
	}

	public void preVisit(IntVariable intVariable) throws VisitorException {
		preVisit((Variable) intVariable);
	}
	
	public void preVisit(BitVectorVariable bvVariable) throws VisitorException {
		preVisit((Variable) bvVariable);
	}

	public void preVisit(Operation operation) throws VisitorException {
		preVisit((Expression) operation);
	}

	public void preVisit(RealConstant realConstant) throws VisitorException {
		preVisit((Constant) realConstant);
	}

	public void preVisit(RealVariable realVariable) throws VisitorException {
		preVisit((Variable) realVariable);
	}

	public void preVisit(StringConstant stringConstant) throws VisitorException {
		preVisit((Constant) stringConstant);
	}

	public void preVisit(StringVariable stringVariable) throws VisitorException {
		preVisit((Variable) stringVariable);
	}
	
	public void ptrVisit(BitVectorConstant bvConstant) throws VisitorException {
		preVisit((Constant) bvConstant);
	}
	
	public void preVisit(ArrayVariable aVariable) throws VisitorException {
		preVisit((Variable) aVariable);
	}

	public void preVisit(Variable variable) throws VisitorException {
		preVisit((Expression) variable);
	}

	public void postVisit(Constant constant) throws VisitorException {
		postVisit((Expression) constant);
	}

	public void postVisit(Expression expression) throws VisitorException {
	}

	public void postVisit(IntConstant intConstant) throws VisitorException {
		postVisit((Constant) intConstant);
	}

	public void postVisit(IntVariable intVariable) throws VisitorException {
		postVisit((Variable) intVariable);
	}
	
	public void postVisit(BitVectorVariable bvVariable) throws VisitorException {
		postVisit((Variable) bvVariable);
	}

	public void postVisit(Operation operation) throws VisitorException {
		postVisit((Expression) operation);
	}

	public void postVisit(RealConstant realConstant) throws VisitorException {
		postVisit((Constant) realConstant);
	}

	public void postVisit(RealVariable realVariable) throws VisitorException {
		postVisit((Variable) realVariable);
	}

	public void postVisit(StringConstant stringConstant) throws VisitorException {
		postVisit((Constant) stringConstant);
	}

	public void postVisit(StringVariable stringVariable) throws VisitorException {
		postVisit((Variable) stringVariable);
	}
	
	public void postVisit(BitVectorConstant bvConstant) throws VisitorException {
		postVisit((Constant) bvConstant);
	}
	
	public void postVisit(ArrayVariable aVariable) throws VisitorException {
		postVisit((Variable) aVariable);
	}

	public void postVisit(Variable variable) throws VisitorException {
		postVisit((Expression) variable);
	}

	
	/*
	 * Eric's additions
	 */
	public void preVisit(Alias alias) throws VisitorException{
		preVisit((Expression) alias);
	}
	
	public void postVisit(Alias alias) throws VisitorException{
		postVisit((Expression) alias);
	}
}
