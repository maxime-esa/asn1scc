using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Antlr.Runtime.Tree;
using Antlr.Runtime;
using Antlr.Asn1;
using Antlr.Acn;
using System.IO;

namespace Antlr
{
    public class Comment
    {
        public static string[] GetComments(IToken[] FileTokens, List<IToken> alreadyTakenComments, int lastTokenLineNo,
            int prevTokenIndex, int nextTokenIndex, bool acn = false)
        {
            List<string> comments = new List<string>();
            int WS = acn ? acnLexer.WS : asn1Lexer.WS;
            int COMMENT = acn ? acnLexer.COMMENT : asn1Lexer.COMMENT;
            int COMMENT2 = acn ? acnLexer.COMMENT2 : asn1Lexer.COMMENT2;

            //first see if there comments on the same line

            while (nextTokenIndex >= 0 && nextTokenIndex < FileTokens.Length)
            {
                IToken t = FileTokens[nextTokenIndex++];
                if (alreadyTakenComments.Contains(t))
                {
                    break;
                }
                if (t.Line != lastTokenLineNo)
                {
                    break;
                }
                if (t.Type == WS)
                {
                    continue;
                }
                else if (t.Type == COMMENT || t.Type == COMMENT2)
                {
                        comments.Insert(0, t.Text);
                        alreadyTakenComments.Add(t);
                }
                else
                {
                    break;
                }

            }

            //if no comments were found at the same line, then look back (above)
            if (comments.Count == 0)
            {

                while (prevTokenIndex >= 0 && prevTokenIndex < FileTokens.Length)
                {
                    IToken t = FileTokens[prevTokenIndex--];
                    if (alreadyTakenComments.Contains(t))
                        break;
                    if (t.Type == WS)
                        continue;
                    else if (t.Type == COMMENT || t.Type == COMMENT2)
                    {
                            comments.Insert(0, t.Text);
                            alreadyTakenComments.Add(t);
                    }
                    else
                        break;
                }
            }

            return comments.ToArray();
        }
    }



    public class Html
    {
        public static string[] m_asn1Tokens = {
            "PLUS-INFINITY", "MINUS-INFINITY", "GeneralizedTime", "UTCTime", "mantissa", "base", "exponent", "UNION", "INTERSECTION",
            "DEFINITIONS", "EXPLICIT", "TAGS", "IMPLICIT", "AUTOMATIC", "EXTENSIBILITY", "IMPLIED", "BEGIN", "END", "EXPORTS", "ALL",
            "IMPORTS", "FROM", "UNIVERSAL", "APPLICATION", "PRIVATE", "BIT", "STRING", "BOOLEAN", "ENUMERATED", "INTEGER", "REAL",
            "OPTIONAL", "SIZE", "OCTET", "MIN", "MAX", "TRUE", "FALSE", "ABSENT", "PRESENT", "WITH",
            "COMPONENT", "DEFAULT", "NULL", "PATTERN", "OBJECT", "IDENTIFIER", "RELATIVE-OID", "NumericString",
            "PrintableString", "VisibleString", "IA5String", "TeletexString", "VideotexString", "GraphicString", "GeneralString",
            "UniversalString", "BMPString", "UTF8String", "INCLUDES", "EXCEPT", "SET", "SEQUENCE","CHOICE","OF","COMPONENTS"
            };

        public static string[] m_acnKeywords = {
            "endianness", "big", "little", "encoding", "pos-int", "twos-complement", "BCD", "ASCII",
            "IEEE754-1985-32", "IEEE754-1985-64", "size", "null-terminated", "align-to-next", "byte",
            "word", "dword", "encode-values", "true-value", "false-value", "pattern", "present-when",
            "determinant", "DEFINITIONS", "BEGIN", "END", "CONSTANT", "NOT", "INTEGER", "BOOLEAN", "NULL"
            };

        static string getSafeText(IToken t)
        {
            return t.Text.Replace("<", "&lt;").Replace(">", "&gt");
        }
        public static string getAsn1InHtml(IToken[] asn1FileTokens, string[] tasNames, System.Tuple<string,int,int>[] blueTassesWithLoc)
        {
            System.IO.StringWriter strm = new StringWriter();

            for (int i = 0; i < asn1FileTokens.Length; i++)
            {
                IToken t = asn1FileTokens[i];
                var line = t.Line;
                var charPos = t.CharPositionInLine;
                var blueTas = blueTassesWithLoc.FirstOrDefault(x => x.Item2 == line && x.Item3 == charPos);

                if (blueTas!=null)
                    strm.Write("<a name=\"ASN1_" + blueTas.Item1.Replace("-", "_") + "\">" + getSafeText(t) + "</a>");
                else if (m_asn1Tokens.Contains(t.Text))
                    strm.Write("<b><font  color=\"#5F9EA0\" >" + getSafeText(t) + "</font></b>");
                else if (t.Type == asn1Lexer.StringLiteral || t.Type == asn1Lexer.OctectStringLiteral || t.Type == asn1Lexer.BitStringLiteral)
                    strm.Write("<font  color=\"#A31515\" >" + getSafeText(t) + "</font>");
                else if (t.Type == asn1Lexer.UID && tasNames.Contains(t.Text))
                {
                    int j = i + 1;
                    // increment j until a non WS/Comment is found (find first "real" token forward)
                    while (j < asn1FileTokens.Length)
                        if (asn1FileTokens[j].Type == asn1Lexer.WS || asn1FileTokens[j].Type == asn1Lexer.COMMENT || asn1FileTokens[j].Type == asn1Lexer.COMMENT2)
                            j++;
                        else
                            break;
                    int k = i - 1;
                    // find backward the first non-WS/Comment token
                    while (k > 0)
                        if (asn1FileTokens[k].Type == asn1Lexer.WS || asn1FileTokens[k].Type == asn1Lexer.COMMENT || asn1FileTokens[k].Type == asn1Lexer.COMMENT2)
                            k--;
                        else
                            break;
                    // new Type Assignment (followed by ::= and not following a lid, that would correspond to value assignment)
                    if (asn1FileTokens[j].Type == asn1Lexer.ASSIG_OP && asn1FileTokens[k].Type != asn1Lexer.LID)
                        strm.Write("<a name=\"ASN1_" + getSafeText(t).Replace("-", "_") + "\"></a><a href=\"#ICD_" + getSafeText(t).Replace("-", "_") + "\"><font  color=\"#B8860B\" ><b>" + getSafeText(t) + "</b></font></a>");
                    else
                        strm.Write("<a href=\"#ASN1_" + getSafeText(t).Replace("-", "_") + "\"><font  color=\"#000000\" >" + getSafeText(t) + "</font></a>");
                }
                else if (t.Type == asn1Lexer.COMMENT || t.Type == asn1Lexer.COMMENT2)
                    strm.Write("<font  color=\"#008000\" ><i>" + getSafeText(t) + "</i></font>");
                else
                    strm.Write(getSafeText(t));
            }

            return strm.ToString();
        }

    }
}
