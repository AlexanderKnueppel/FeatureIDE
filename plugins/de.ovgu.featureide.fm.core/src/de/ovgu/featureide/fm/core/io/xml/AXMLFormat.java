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
package de.ovgu.featureide.fm.core.io.xml;

import static de.ovgu.featureide.fm.core.localization.StringTable.YES;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParserFactory;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.TransformerFactoryConfigurationError;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.Attributes;
import org.xml.sax.InputSource;
import org.xml.sax.Locator;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.Problem.Severity;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Prints a feature model in XML format.
 * 
 * @author Sebastian Krieter
 */
public abstract class AXMLFormat<T> implements IPersistentFormat<T>, XMLFeatureModelTags {

	private static final String SUFFIX = "xml";

	private static final String LINE_NUMBER_KEY_NAME = "lineNumber";

	protected T object;

	public static Document readXML(CharSequence source) throws IOException, SAXException, ParserConfigurationException {
		final Document doc = DocumentBuilderFactory.newInstance().newDocumentBuilder().newDocument();
		final LinkedList<Element> elementStack = new LinkedList<>();
		final StringBuilder textBuffer = new StringBuilder();

		final DefaultHandler handler = new DefaultHandler() {
			private Locator locator;

			@Override
			public void characters(final char ch[], final int start, final int length) throws SAXException {
				textBuffer.append(ch, start, length);
			}

			@Override
			public void endElement(final String uri, final String localName, final String qName) {
				addTextIfNeeded();
				final Element closedEl = elementStack.pop();
				if (elementStack.isEmpty()) { // Is this the root element?
					doc.appendChild(closedEl);
				} else {
					final Element parentEl = elementStack.peek();
					parentEl.appendChild(closedEl);
				}
			}

			@Override
			public void setDocumentLocator(final Locator locator) {
				this.locator = locator;
			}

			@Override
			public void startElement(final String uri, final String localName, final String qName, final Attributes attributes) throws SAXException {
				addTextIfNeeded();
				final Element el = doc.createElement(qName);
				for (int i = 0; i < attributes.getLength(); i++) {
					el.setAttribute(attributes.getQName(i), attributes.getValue(i));
				}
				el.setUserData(LINE_NUMBER_KEY_NAME, String.valueOf(this.locator.getLineNumber()), null);
				elementStack.push(el);
			}

			private void addTextIfNeeded() {
				if (textBuffer.length() > 0) {
					final Element el = elementStack.peek();
					final Node textNode = doc.createTextNode(textBuffer.toString());
					el.appendChild(textNode);
					textBuffer.delete(0, textBuffer.length());
				}
			}
		};

		final InputSource inputSource = new InputSource(new StringReader(source.toString()));
		SAXParserFactory.newInstance().newSAXParser().parse(inputSource, handler);
		return doc;
	}

	/**
	 * @param nodeList
	 * @return The child nodes from type Element of the given NodeList.
	 */
	protected static final List<Element> getElements(NodeList nodeList) {
		final ArrayList<Element> elements = new ArrayList<>(nodeList.getLength());
		for (int temp = 0; temp < nodeList.getLength(); temp++) {
			final org.w3c.dom.Node nNode = nodeList.item(temp);
			if (nNode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				final Element eElement = (Element) nNode;
				elements.add(eElement);
			}
		}
		return elements;
	}

	/**
	 * Inserts indentations into the text
	 * 
	 * @param text
	 * @return
	 */
	private static String prettyPrint(String text) {
		final StringBuilder result = new StringBuilder();
		String line;
		int indentLevel = 0;
		final BufferedReader reader = new BufferedReader(new StringReader(text));
		try {
			line = reader.readLine();
			while (line != null) {
				if (line.startsWith("</")) {
					indentLevel--;
					for (int i = 0; i < indentLevel; i++) {
						result.append("\t");
					}
				}

				else if (line.startsWith("<")) {
					for (int i = 0; i < indentLevel; i++) {
						result.append("\t");
					}
					if (!line.contains("</")) {
						indentLevel++;
					}
				} else {
					for (int i = 0; i < indentLevel; i++) {
						result.append("\t");
					}
				}
				result.append(line + "\n");
				if (line.contains("/>")) {
					indentLevel--;
				}
				line = reader.readLine();
			}
		} catch (final IOException e) {
			Logger.logError(e);
		}
		return result.toString();
	}

	@Override
	public String getSuffix() {
		return SUFFIX;
	}

	@Override
	public ProblemList read(T object, CharSequence source) {
		this.object = object;
		final ProblemList lastWarnings = new ProblemList();
		try {
			final Document doc = readXML(source);
			doc.getDocumentElement().normalize();
			readDocument(doc, lastWarnings);
		} catch (SAXException e) {
			//TODO add line information, if any
			lastWarnings.add(new Problem(e));
		} catch (UnsupportedModelException e) {
			Logger.logError(e);
			lastWarnings.add(new Problem(e.getMessage(), e.lineNumber, Severity.ERROR));
		} catch (IOException | ParserConfigurationException e) {
			Logger.logError(e);
			lastWarnings.add(new Problem(e.getMessage(), 0, Severity.ERROR));
		} catch (Exception e) {
			Logger.logError(e);
			lastWarnings.add(new Problem(e.getMessage(), 0, Severity.ERROR));
		}

		return lastWarnings;
	}

	@Override
	public String write(T object) {
		this.object = object;
		//Create Empty DOM Document
		final DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
		dbf.setNamespaceAware(true);
		dbf.setIgnoringComments(true);
		dbf.setIgnoringElementContentWhitespace(false);
		dbf.setCoalescing(true);
		dbf.setExpandEntityReferences(true);
		DocumentBuilder db = null;
		try {
			db = dbf.newDocumentBuilder();
		} catch (final ParserConfigurationException pce) {
			Logger.logError(pce);
		}
		final Document doc = db.newDocument();
		//Create the XML Representation
		writeDocument(doc);

		//Transform the XML Representation into a String
		Transformer transfo = null;
		try {
			transfo = TransformerFactory.newInstance().newTransformer();
		} catch (final TransformerConfigurationException e) {
			Logger.logError(e);
		} catch (final TransformerFactoryConfigurationError e) {
			Logger.logError(e);
		}

		transfo.setOutputProperty(OutputKeys.METHOD, SUFFIX);
		transfo.setOutputProperty(OutputKeys.INDENT, YES);
		final StreamResult result = new StreamResult(new StringWriter());
		final DOMSource source = new DOMSource(doc);
		try {
			transfo.transform(source, result);
		} catch (final TransformerException e) {
			Logger.logError(e);
		}

		return prettyPrint(result.getWriter().toString());
	}

	/**
	 * Reads an XML-Document.
	 * 
	 * @param doc document to read
	 * @param warnings list of warnings / errors that occur during read
	 */
	protected abstract void readDocument(Document doc, List<Problem> warnings) throws UnsupportedModelException;

	/**
	 * Writes an XML-Document.
	 * 
	 * @param doc document to write
	 */
	protected abstract void writeDocument(Document doc);

}
