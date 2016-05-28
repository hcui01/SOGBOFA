package rddl.policy;

import java.security.AllPermission;
import java.util.*;

import javax.swing.plaf.basic.BasicInternalFrameTitlePane.MaximizeAction;

import org.apache.xerces.impl.xpath.XPath.Step;





import rddl.EvalException;
import rddl.RDDL;
import rddl.RDDL.*;
import rddl.State;
import rddl.parser.parser;
import rddl.viz.GenericScreenDisplay;
import rddl.viz.NullScreenDisplay;
import rddl.viz.StateViz;
import rddl.RDDL.DOMAIN;
import rddl.RDDL.INSTANCE;
import rddl.RDDL.ENUM_TYPE_DEF;
import rddl.RDDL.LCONST;
import rddl.RDDL.LVAR;
import rddl.RDDL.PVARIABLE_DEF;
import rddl.RDDL.PVAR_INST_DEF;
import rddl.RDDL.PVAR_NAME;
import util.Permutation;

public class YNNR14 extends Policy{
	
	public YNNR14 () { 
		super();
	}
	
	public YNNR14(String instance_name) {
		super(instance_name);
	}
	
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
		_visCounter.SeenTime ++;
		INSTANCE instance = rddl._tmInstanceNodes.get(_sInstanceName);
		DOMAIN domain = rddl._tmDomainNodes.get(instance._sDomain);
		//System.out.println(s);
		TreeSearch searchEngine = new TreeSearch(s, _random, instance, false, false, domain);
		long t0 = System.currentTimeMillis();
		while(System.currentTimeMillis() - t0 < _timeAllowed){
			searchEngine.Traverse();
		}
		if(ifPrint){
			System.out.println("MAX depth: " + searchEngine.maxDepth);
		}
		_visCounter.SeenInTotal += searchEngine.root.perfRec.size();
		return searchEngine.root.perfRec.get(searchEngine.root.bestChild).action.action;
	}
}


