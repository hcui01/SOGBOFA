package rddl.policy;

import java.util.ArrayList;
import rddl.TreeExp;

public class TreeSizeCounter {
	ArrayList<TreeExp> ifVisited = new ArrayList<>();
	long nonLeafCounter = 0;
	void Count(TreeExp F) {
		ArrayList<TreeExp> queue = new ArrayList<>();
		queue.add(F);
		int index = 0;
		while(index < queue.size()) {
			TreeExp currentNode = queue.get(index);
			if(ifVisited.contains(currentNode)) {
				index ++;
				continue;
			}
			if(currentNode.subExp != null && currentNode.subExp.size() > 0) {
				//nonLeafCounter += currentNode.father.size();
				nonLeafCounter ++;
				
				for(TreeExp theChild: currentNode.subExp) {
					if (!queue.contains(theChild)){
						queue.add(theChild);
					}
				}
			}
			
			if(currentNode.term != null && currentNode.term.var != -1) {
				//nonLeafCounter += currentNode.father.size();
				nonLeafCounter ++;
			}
			
			//if(currentNode.father != null && currentNode.father.size() > 0) {
			//	nonLeafCounter += currentNode.father.size();
			//}
			/*
			if(currentNode.subExp == null) {
				nonLeafCounter ++;
			}
			*/
			ifVisited.add(currentNode);
			index ++;
		}
	}
}
