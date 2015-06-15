package za.ac.sun.cs.green.service.z3;

import java.util.Properties;
import java.util.Set;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.service.SATService;

public class SATZ3NativeService extends SATService {

	private SubsumptionHelper sh;
	
	public SATZ3NativeService(Green solver, Properties properties) {
		super(solver);
		sh = new SubsumptionHelper();
	}
	
	@Override
	protected Boolean solve(Instance instance) {
		return sh.solve(instance.getExpression());
	}
}

