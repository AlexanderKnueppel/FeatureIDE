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
package de.ovgu.featureide.core.featurehouse.proofautomation.model;

import java.util.ArrayList;
import java.util.List;

/**
 * This class has the informations for a java method
 * 
 * @author marlen
 */
public class Method {
	String name = "";
	public List<String> parameter = new ArrayList<String>();
	public List<String> fields = new ArrayList<String>();
	List<String>calledMethod = new ArrayList<String>();

	String original = "";
	String feature = "";
	String rootFeature = "";
	
		/**
	 * @return the calledMethod
	 */
	public List<String> getCalledMethod() {
		return calledMethod;
	}

	/**
	 * @param calledMethod the calledMethod to set
	 */
	public void setCalledMethod(List<String> calledMethod) {
		this.calledMethod = calledMethod;
	}
	/**
	 * @return the rootFeature
	 */
	public String getRootFeature() {
		return rootFeature;
	}

	/**
	 * @param rootFeature the rootFeature to set
	 */
	public void setRootFeature(String rootFeature) {
		this.rootFeature = rootFeature;
	}

	/**
	 * @return the feature
	 */
	public String getFeature() {
		return feature;
	}

	/**
	 * @param feature the feature to set
	 */
	public void setFeature(String feature) {
		this.feature = feature;
	}

	/**
	 * @return the originalString
	 */
	public String getOriginal() {
		return original;
	}

	/**
	 * @param originalString the originalString to set
	 */
	public void setOriginal(String original) {
		this.original = original;
	}
	
	public boolean hasOriginal() {
		if(!original.isEmpty()) {
			return true;
		}else {
			return false;
		}
	}

	/**
	 * @param name
	 * @param parameter
	 * @param variables
	 */
	public Method(String name, List<String> parameter, List<String> variables, List<String> calledMethod,String original,String feature) {
		super();
		this.name = name;
		this.parameter = parameter;
		this.fields = variables;
		this.calledMethod = calledMethod;
		this.original = original;
		this.feature = feature;
	}
	
	public Method() {};
	
	/**
	 * @return the name
	 */
	public String getName() {
		return name;
	}
	/**
	 * @param name the name to set
	 */
	public void setName(String name) {
		this.name = name;
	}
	/**
	 * @return the parameter
	 */
	public List<String> getParameter() {
		return parameter;
	}
	/**
	 * @param parameter the parameter to set
	 */
	public void setParameter(List<String> parameter) {
		this.parameter = parameter;
	}
	/**
	 * @return the variables
	 */
	public List<String> getFields() {
		return fields;
	}
	/**
	 * @param variables the variables to set
	 */
	public void setFields(List<String> fields) {
		this.fields = fields;
	}

	

}
