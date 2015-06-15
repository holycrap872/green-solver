package za.ac.sun.cs.green.service.bvfactorizer;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.Service;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.resources.Pair;
import za.ac.sun.cs.green.service.BasicService;
import za.ac.sun.cs.green.util.Reporter;

public class SATBVFactorizerService extends BasicService {

	private static final String BVFACTORS = "BVFACTORS";
	private static final String BVFACTORS_UNSOLVED = "BVFACTORS_UNSOLVED";

	/**
	 * Number of times the slicer has been invoked.
	 */
	private int invocationCount = 0;

	/**
	 * Total number of constraints processed.
	 */
	private int constraintCount = 0;

	/**
	 * Number of factored constraints returned.
	 */
	private int factorCount = 0;

	/**
	 * Used exclusively by UndeterminedArrayMerger if user decides to try and prove that
	 * to factors that would traditionally be merged due to a symbolic access can be proven
	 * to be separate.
	 */
	public SATBVFactorizerService(Green solver) {
		super(solver);
	}

	@Override
	public Set<Instance> processRequest(Instance instance) {
		@SuppressWarnings("unchecked")
		//Checks to see if already computed by referencing map in instance 
		Set<Instance> result = (Set<Instance>) instance.getData(BVFACTORS);
		if (result == null) {
			final Instance p = instance.getParent();

			BVFactorExpression fc0 = null;
			if (p != null) {
				fc0 = (BVFactorExpression) p.getData(BVFactorExpression.class);
				if (fc0 == null) {
					// Construct the parent's factor and store it
					fc0 = new BVFactorExpression(solver, null, p.getFullExpression(), solver.getPropertiesFile());
					p.setData(BVFactorExpression.class, fc0);
				}
			}

			final BVFactorExpression fc = new BVFactorExpression(solver, fc0, instance.getExpression(), solver.getPropertiesFile());
			instance.setData(BVFactorExpression.class, fc);

			result = new HashSet<Instance>();
			for (Expression e : fc.getFactors()) {
				System.out.println("BVFactorizer computes instance for :" + e+"\n");
				final Instance i = new Instance(getSolver(), instance.getSource(), null, e);
				result.add(i);
			}
			result = Collections.unmodifiableSet(result);
			instance.setData(BVFACTORS, result);	//Adds the factors to the particular instance 
			instance.setData(BVFACTORS_UNSOLVED, new HashSet<Instance>(result));

			System.out.println("Factorize exiting with " + result.size() + " results");

			constraintCount += 1;
			factorCount += fc.getNumFactors();
		}
		return result;
	}

	@Override
	public Object childDone(Instance instance, Service subservice, Instance subinstance, Object result) {
		Boolean issat = (Boolean) result;
		if ((issat != null) && !issat) {
			return false;
		}
		@SuppressWarnings("unchecked")
		HashSet<Instance> unsolved = (HashSet<Instance>) instance.getData(BVFACTORS_UNSOLVED);
		if (unsolved.contains(subinstance)) {
			// Remove the subinstance now that it is solved 
			unsolved.remove(subinstance);
			instance.setData(BVFACTORS_UNSOLVED, unsolved);
			// Return true of no more unsolved factors; else return null to carry on the computation
			return (unsolved.isEmpty()) ? result : null; 
		} else {
			// We have already solved this sub-instance; return null to carry on the computation
			return null;
		}
	}

	@Override
	public void report(Reporter reporter) {
		reporter.report(getClass().getSimpleName(), "invocations = " + invocationCount);
		reporter.report(getClass().getSimpleName(), "totalConstraints = " + constraintCount);
		reporter.report(getClass().getSimpleName(), "bvfactoredConstraints = " + factorCount);
	}

}
