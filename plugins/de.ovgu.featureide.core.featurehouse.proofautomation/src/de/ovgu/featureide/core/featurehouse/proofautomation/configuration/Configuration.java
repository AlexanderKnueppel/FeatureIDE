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
package de.ovgu.featureide.core.featurehouse.proofautomation.configuration;

/**
 * Contains the configuration variables
 * 
 * @author Stefanie
 */
public class Configuration {
	public static String keyBinPath = "D:\\Programme\\Eclipse Umgebungen\\eclipse mars\\key\\system\\binary"; //contains the key binary path (usually system\binary)
	public static String keyLibsPath = "D:\\Programme\\Eclipse Umgebungen\\eclipse mars\\key\\key-ext-jars"; //contains the key library path (usually key-ext-jars)
	public static int maxRuleApplication = 10000;
	public static boolean excludeMain = true; //excludes the proofs of class main
	public static String excludedClass ="Main";
	public static boolean excludeFailedProofs = true; //if true the failed Proofs are removed from the total results
	public static boolean proveDispatcher = false; //if true, the dispatcher Methods are proven else not
	public static boolean performVerification = true; //performs Verification only if true
	public static boolean generateMetaproduct = true; //
}
