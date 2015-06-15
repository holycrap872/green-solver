package za.ac.sun.cs.green.service.bvrenamer;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.service.BasicService;
import za.ac.sun.cs.green.util.Reporter;

public class SATBVRenamerService extends BasicService{
	
	private static final String BVRENAMED = "BVRENAMED";

	/**
	 * Number of times the renamer has been invoked.
	 */
	private int invocationCount = 0;

	/**
	 * Total number of constraints processed.
	 */
	private int constraintCount = 0;
	
	/**
	 * Total number of variables renamed
	 */
	private int varRenamed = 0;

	public SATBVRenamerService(Green solver){
		super(solver);
	}
	
	@Override
	public Set<Instance> processRequest(Instance instance){
		@SuppressWarnings("unchecked")
		Set<Instance> result = (Set<Instance>) instance.getData(BVRENAMED);	//Checks to see if already computed by referencing map in instance 
		if (result == null) {
			try{
				final Instance p = instance.getParent();

				BVRenameExpression rn0 = null;
				//If there is a parent
				if (p != null) {
					rn0 = (BVRenameExpression) p.getData(BVRenameExpression.class);
					if (rn0 == null) {
						// Construct the parent's factor and store it
						rn0 = new BVRenameExpression(null, p.getFullExpression());
						p.setData(BVRenameExpression.class, rn0);
					}
				}

				/*
				 * Add the renamed expression to the instance.
				 */
				final BVRenameExpression rn = new BVRenameExpression(rn0, instance.getExpression());
				instance.setData(BVRenameExpression.class, rn);

				result = new HashSet<Instance>();
				Expression e = rn.getRenamedExpression();

//				System.out.println("Renamer computes instance for :" + e+"\n");
				final Instance i = new Instance(getSolver(), instance.getSource(), null, e);
				result.add(i);

				result = Collections.unmodifiableSet(result);
				instance.setData(BVRENAMED, result);	//Adds the factors to the particular instance 

				constraintCount += 1;
				varRenamed += rn.getNumFactors();
			}catch(Exception e){
				System.out.println("Failed on: "+instance.toString());
				e.printStackTrace();
				System.exit(1);
			}

		}
		return result;
	}
	
	@Override
	public Object allChildrenDone(Instance instance, Object result) {
		Instance original = instance.getSource();
		@SuppressWarnings("unchecked")
		Set<Instance> factors = (Set<Instance>) instance.getData(BVRENAMED);
		@SuppressWarnings("unchecked")
		Set<Instance> ret = (Set<Instance>) original.getData(BVRENAMED);
		if (ret == null) {
			ret = new HashSet<Instance>();
		}
		ret.addAll(factors);
		original.setData(BVRENAMED, ret);
		
		return result;
	}
	

	@Override
	public void report(Reporter reporter) {
		reporter.report(getClass().getSimpleName(), "invocations = " + invocationCount);
		reporter.report(getClass().getSimpleName(), "totalConstraints = " + constraintCount);
		reporter.report(getClass().getSimpleName(), "variablesRenamed = " + varRenamed);
	}
	
	

}
