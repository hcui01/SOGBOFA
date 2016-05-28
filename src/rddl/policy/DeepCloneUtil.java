package rddl.policy;

import java.io.*;

public class DeepCloneUtil {
	public static Object deepClone(Object obj) {
		try {
			// 将对象写到流里
			ByteArrayOutputStream bo = new ByteArrayOutputStream();
			ObjectOutputStream oo  = new ObjectOutputStream(bo);
			oo.writeObject(obj);
			// 从流里读出来
			ByteArrayInputStream bi = new ByteArrayInputStream(bo.toByteArray());
			ObjectInputStream oi = new ObjectInputStream(bi);
			return (oi.readObject());
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}
}