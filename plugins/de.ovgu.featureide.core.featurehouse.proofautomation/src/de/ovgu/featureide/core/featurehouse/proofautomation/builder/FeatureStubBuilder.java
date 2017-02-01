/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.featurehouse.proofautomation.builder;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.LinkedList;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.meta.FeatureStubsGenerator;

public class FeatureStubBuilder {
	
	public static void generateAllFeatureStubsForApproach(LinkedList<IProject> projects){
		for(IProject p: projects){
			try{
			IFeatureProject f = CorePlugin.getFeatureProject(p);
			FeatureStubsGenerator fsg = new FeatureStubsGenerator(f);
			fsg.generate();
			}catch (Exception e){
				System.out.println("Error creating featurestub for project "+p.getName());
				e.printStackTrace();
			}
		}
	}
	
	public static void prepareForVerification(File transactionAccount, File lockAccount){
		addField("int","balance",null,transactionAccount);
		addField("int","OVERDRAFT_LIMIT",null,transactionAccount);
		addField("boolean","lock",null,transactionAccount);
		addField("int[]","updates","new int[10]",transactionAccount);
		addField("int[]","undoUpdates","new int[10]",transactionAccount);
		replaceLockREA(transactionAccount);
		BuilderUtil.removeBracketsOfVar(lockAccount, "lock");
	}
	
	public static void addField(String type, String name,String init,File f){
		if(!checkForField(type,name,f)){
			insertField(type,name,init,f);
		}
	}

	public static boolean checkForField(String type,String name,File f){
		type = type.replaceAll("\\[", "\\\\[");
		type = type.replaceAll("\\]", "\\\\]");
		String fieldPattern ="\\s*(public|private|protected)\\s*"+type+"\\s*"+name+".*";
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(f));
			String line = bReader.readLine();
			while (line != null){     
				if(Pattern.matches(fieldPattern, line)){
					return true;
			    }
			    line = bReader.readLine();
			}
			bReader.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		return false;
	}
	
	public static void insertField(String type, String name,String init, File f){
		String field;
		if(init==null){
			field = "public "+type+" "+name+"; //Auto-generated field for key verification";
		}
		else{
			field = "public "+type+" "+name+" = "+init+"; //Auto-generated field for key verification";
		}
		StringBuffer sbuffer = new StringBuffer();
		boolean added= false;
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(f));
            String line = bReader.readLine();
            while(line != null) {
            	sbuffer.append(line + System.getProperty("line.separator"));
                if(line.contains("class ")&&!added) {
                	sbuffer.append(field + System.getProperty("line.separator"));
                	added = true;
                }
                line = bReader.readLine();
            }
            bReader.close();
        } catch(IOException e) {
            e.printStackTrace();
        }
        BuilderUtil.rewriteFile(sbuffer,f);
		
	}
	
	public static void replaceLockREA(File f){
		StringBuffer sbuffer = new StringBuffer();
		String lockPattern = "\\s*@\\s*(requires_abs|ensures_abs|assignable_abs)\\s*lock(R|E|A)\\s*;.*";
		try {
			BufferedReader bReader = new BufferedReader(new FileReader(f));
            String line = bReader.readLine();
            while(line != null) {
            	if(Pattern.matches(lockPattern, line)){
            		line = line.replace("lock", "lockAcc");
                }
            	sbuffer.append(line + System.getProperty("line.separator"));
                line = bReader.readLine();
            }
            bReader.close();
        } catch(IOException e) {
            e.printStackTrace();
        }
        BuilderUtil.rewriteFile(sbuffer,f);
	}
}
