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
package de.ovgu.featureide.core.featurehouse.proofautomation.key;

import java.io.File;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.BuildMap;
import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.ovgu.featureide.core.featurehouse.proofautomation.evaluation.SingleApproachEvaluation;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.FillMethodMap;

/**
 * This class starts a new JVM to avoid the key memory leak
 * therefore it needs the key library and the key binary path to start a new program instance correct
 * for correct usage the eclipse part of the program is not used in the JVM
 * 
 * @author Stefanie
 * @author Marlen Herter-Bernier 10.2020
 */
public class startNewJVM {
	private static final String FILE_SEPERATOR = System.getProperty("file.separator");
	private static final String PATH_SEPERATOR = System.getProperty("path.separator");
	/**
	 * Starts the evaluation for a single project
	 * @param args [0] contains project path [1] contains the evaluation path
	 */
	public static void main(String[] args) {
		if(args.length >=2 && args[0]!=null && args[1]!=null){
			SingleApproachEvaluation s = new SingleApproachEvaluation(new File(args[0]),0,args[1], args[2],args[3]);
			s.methodMap = FillMethodMap.fillMethodMap(new File(s.evaluatePath.getAbsolutePath()+FILE_SEPERATOR+"methodMap.csv"));
			//SingleProject s = new SingleProject(new File(args[0]),0,args[1]);
			s.performEvaluation();
		}
	}
	
	/**
	 * Starts a new JVM for the evaluation of a single project
	 * Redirects the Error and Output to the evaluation directory
	 * @param projectForEvaluation
	 * @param evalPath
	 * @param evolutionType 
	 */
	public static void startNewProcess(File projectForEvaluation, File evalPath, String method, String evolutionType){
		String projectPath = startNewJVM.class.getProtectionDomain().getCodeSource().getLocation().getPath();
		String binPath = projectPath + "bin";
		String excelLibs = getDirContent(new File(projectPath+FILE_SEPERATOR+"lib"));
	    String keyPath = Configuration.keyPath;
	    String classname = startNewJVM.class.getName();
	    ProcessBuilder processBuilder = 
                new ProcessBuilder("java", "-cp",excelLibs+PATH_SEPERATOR
                		+keyPath+PATH_SEPERATOR
                		+binPath,
                		classname,
                		projectForEvaluation.getAbsolutePath(), 
                		evalPath.getAbsolutePath(),method,evolutionType)
                .inheritIO();	
	    processBuilder.redirectError(new File(evalPath.getAbsolutePath()+FILE_SEPERATOR+"Error.txt"));
	    processBuilder.redirectOutput(new File(evalPath.getAbsolutePath()+FILE_SEPERATOR+"Output.txt"));
	    try{
	    	Process process = processBuilder.start();
	    	process.waitFor();
	    } catch (Exception e){
	    	e.printStackTrace();
	    }
	}
	
	/**
	 * Searches a directory for all libraries 
	 * @param dir
	 * @return
	 */
	private static String getDirContent(File dir){
		String paths = "";
		File[] dirContent = dir.listFiles();
		for(File f: dirContent){
			if(f.isDirectory()){
				paths += getDirContent(f);
			}
			else{
				paths += f.getAbsolutePath()+PATH_SEPERATOR;
			}
		}
		return paths;
	}

}
