package rddl.policy;


import java.util.*;
import rddl.RDDL.PVAR_INST_DEF;


class AssemblyDemo {
    List<PVAR_INST_DEF[]> combination(PVAR_INST_DEF[] a, int m) {
        AssemblyDemo c = new AssemblyDemo();
        List<PVAR_INST_DEF[]> list = new ArrayList<PVAR_INST_DEF[]>();
        int n = a.length;
        if( n == 0){
        	return list;
        }
        if(m == n){
        	list.add(a);
        	return list;
        }
        boolean end = false;
        int[] tempNum = new int[n];
        for (int i = 0; i < n; i++) {
            if (i < m) {
                tempNum[i] = 1;
  
            } else {
                tempNum[i] = 0;
            }
        }
 
        list.add(c.createResult(a, tempNum, m));
        int k = 0;
        while (!end) {
            boolean findFirst = false;
            boolean swap = false;
            for (int i = 0; i < n; i++) {
                int l = 0;
                if (!findFirst && tempNum[i] == 1) {
                    k = i;
                    findFirst = true;
                }
                if (tempNum[i] == 1 && tempNum[i + 1] == 0) {
                    tempNum[i] = 0;
                    tempNum[i + 1] = 1;
                    swap = true;
                    for (l = 0; l < i - k; l++) { 
                        tempNum[l] = tempNum[k + l];
                    }
                    for (l = i - k; l < i; l++) {
                        tempNum[l] = 0;
                    }
                    if (k == i && i + 1 == n - m) { 
                        end = true;
                    }
                }
                if (swap) {
                    break;
                }
            }
            list.add(c.createResult(a, tempNum, m));
        }
        return list;
    }
  
    public PVAR_INST_DEF[] createResult(PVAR_INST_DEF[] a, int[] temp, int m) {
        PVAR_INST_DEF[] result = new PVAR_INST_DEF[m];
        int j = 0;
        for (int i = 0; i < a.length; i++) {
            if (temp[i] == 1) {
                result[j] = a[i];
                j++;
            }
        }
        return result;
    }
   
    public void print(List<int[]> list) {
        for (int i = 0; i < list.size(); i++) {
            int[] temp = (int[]) list.get(i);
            for (int j = 0; j < temp.length; j++) {
                java.text.DecimalFormat df = new java.text.DecimalFormat("00");
            }
        }
    }
  
    public void printVir(int[] a) {
        for (int i = 0; i < a.length; i++) {
            System.out.print(a[i]);
        }
    }
}