package rddl.policy;

import java.util.ArrayList;

//assume that all actions have the actor as one of their terms
//and the actors is the first appearing in the term list
//otherwise this method cannot be used

import rddl.EvalException;
import rddl.RDDL;
import rddl.State;
import rddl.RDDL.ENUM_TYPE_DEF;
import rddl.RDDL.LCONST;
import rddl.RDDL.PVARIABLE_DEF;
import rddl.RDDL.PVAR_INST_DEF;
import rddl.RDDL.PVAR_NAME;
import util.Permutation;

public class NewRandomPolicy extends Policy {

	@Override
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
		ArrayList<PVAR_INST_DEF> actions = new ArrayList<PVAR_INST_DEF>();
		boolean[] ifHasAction = new boolean[s._nMaxNondefActions+1];
		for(int i = 0; i <= s._nMaxNondefActions; i ++){
			ifHasAction[i] = new Boolean(false);
		}
		PVAR_NAME firstName = s._alActionNames.get(0);
		ArrayList<ArrayList<LCONST>> inst = s.generateAtoms(firstName);
		for(int i = 0; i <= inst.size() - 1; i ++){
			//get the first item of the term list
			ArrayList<LCONST> term = inst.get(i);
			LCONST firstItem = term.get(0);
			//find the number of the actor
			String tail = firstItem.toString();
			int leftIndex;
			for(leftIndex = 0; leftIndex < tail.length(); leftIndex ++){
				if(tail.charAt(leftIndex) >= '0' && tail.charAt(leftIndex) <= '9'){
					break;
				}
			}
			int theActor = Integer.valueOf(tail.substring(leftIndex));
			//try check if the actor has 
			if(!ifHasAction[theActor]){
				//try a random action
				int theAction = _random.nextInt(s._alActionNames.size()+1);
				
				//noop action
				if(theAction == s._alActionNames.size()){
					ifHasAction[theActor] = true;
					continue;
				}
				PVAR_NAME actionName = s._alActionNames.get(theAction);
				
				// IMPORTANT: get random assignment that matches action type
				Object value = new Boolean(true);
				
				// Now set the action
				actions.add(new PVAR_INST_DEF(actionName._sPVarName, value, term));
				boolean passed_constraints = true;
				try {
					s.checkStateActionConstraints(actions);
				} catch (EvalException e) { 
					// Got an eval exception, constraint violated
					passed_constraints = false;
						//System.out.println(actions + " : " + e);
						//System.out.println(s);
						//System.exit(1);
				} catch (Exception e) { 
					// Got a real exception, something is wrong
					System.out.println("\nERROR evaluating constraint on action set: " + 
							actions + /*"\nConstraint: " +*/ e + "\n");
					e.printStackTrace();
					throw new EvalException(e.toString());
				}
				if(passed_constraints){
					ifHasAction[theActor] = true;
				}
				else{
					actions.remove(actions.size()-1);
				}
			}
		}
		// TODO Auto-generated method stub
		return actions;
	}

}
