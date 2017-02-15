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

import de.ovgu.featureide.core.featurehouse.proofautomation.configuration.Configuration;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.SingleProject;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ExitMainAction;

/**
 * TODO description
 * 
 * @author Stefanie
 */
public class startNewJVM {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		if(args.length >=2 && args[0]!=null && args[1]!=null){
			SingleProject s = new SingleProject(new File(args[0]),0,args[1]);
			s.performEvaluation();
		}
		ExitMainAction ema = new ExitMainAction(MainWindow.getInstance());
		ema.exitMainWithoutInteraction();
	}
	
	public static void startNewProcess(File projectForEvaluation, File evalPath){
		String projectPath = startNewJVM.class.getProtectionDomain().getCodeSource().getLocation().getPath();
		String binPath = projectPath +"\\bin";
		String excelLibs = getDirContent(new File(projectPath+"\\lib"));
	    String keyPath = Configuration.keyBinPath;
	    String keyLibs = getDirContent(new File(Configuration.keyLibsPath));
	    String classname = startNewJVM.class.getName();
	    ProcessBuilder processBuilder = 
	                new ProcessBuilder("java", "-cp",excelLibs+keyLibs+";"+keyPath+";"+binPath,classname,projectForEvaluation.getAbsolutePath(), evalPath.getAbsolutePath());
	    processBuilder.redirectError(new File(evalPath.getAbsolutePath()+"\\Error.txt"));
	    processBuilder.redirectOutput(new File(evalPath.getAbsolutePath()+"\\Output.txt"));
	    try{
	    	Process process = processBuilder.start();
	    	process.waitFor();
	    } catch (Exception e){
	    	e.printStackTrace();
	    }
	}
	
	private static String getDirContent(File dir){
		String paths = "";
		File[] dirContent = dir.listFiles();
		for(File f: dirContent){
			if(f.isDirectory()){
				paths += getDirContent(f);
			}
			else{
				paths += f.getAbsolutePath()+";";
			}
		}
		return paths;
	}

}
