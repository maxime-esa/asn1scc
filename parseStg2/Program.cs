using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Xml.Linq;
using System.IO;


/*
 
<Settings>
  <run mode="single">
    <input>ASN.stg</input>
    <output>ASN.stg.fs</output>
    <modName>ASN</modName> 
  </run>
</Settings>
 
 
 */




namespace parseStg2
{

    class Program
    {

        static bool hn(string name, string rule)
        {
            return name.StartsWith(rule) && name.Length > rule.Length && Char.IsUpper(name[rule.Length]);
        }
        
        static string detectTypeByParam(string name)
        {
            string[] knownStrings = { "p", "p1", "p2", "ptr", "i", "v", "v1", "v2", "c1", "c2" };
            if (knownStrings.Contains(name))
                return "string";
            if (name.StartsWith("arr_"))
                return string.Format("seq<{0}>", name.Replace("arr_", ""));

            if (hn(name, "arrs"))
                return "seq<string>";
            if (hn(name, "arrn"))
                return "seq<BigInteger>";
            if (hn(name, "arru"))
                return "seq<byte>";
            if (hn(name, "arro"))
                return "???array<###Object>";
            if (hn(name, "b"))
                return "bool";
            if (hn(name, "s"))
                return "string";
            if (hn(name, "n"))
                return "BigInteger";
            if (hn(name, "d"))
                return "double";
            if (hn(name, "c"))
                return "char";

            return "Object";
        }
        
        class Function
        {
            public string name { get; set; }
            public IEnumerable<string> prms { get; set; }
            public string name2 { get { return name.Replace("_decode", "").Replace("_encode", ""); } }
            public string ID { get { return name2 + prms.Join(""); } }
        }



        static int Main(string[] args)
        {
            var curDir = Path.GetDirectoryName(args[0]);
            XDocument doc = XDocument.Load(args[0]);
            int ret = 0;
            foreach (var elem in doc.Descendants("run"))
            {
                if (elem.Attribute("mode").Value == "single")
                {
                    ret += ProcessSingle(elem, curDir);
                }
                    
            }
            return ret;
        }

        static int ProcessSingle(XElement run, string curDir)
        {
            var inpFileName = Path.Combine(curDir, run.Element("input").Value);
            var outFileName = Path.Combine(curDir, run.Element("output").Value);
            var modName = run.Element("modName").Value;
            var UseAttr = run.Attribute("uses");
            var Uses = UseAttr == null ? new List<string>() { "Ast" } : new List<string>(UseAttr.Value.Split(';').Where(c => c.Trim() != ""));
            string lng = "";
            switch (run.Element("lang").Value.ToUpper())
            {
                case "SPARK":
                    lng = "ST.lang <- Ast.ProgrammingLanguage.Spark";
                    break;
                case "C":
                    lng = "ST.lang <- Ast.ProgrammingLanguage.C";
                    break;
                case "ADA":
                    lng = "ST.lang <- Ast.ProgrammingLanguage.Ada";
                    break;
                case "HTML":
                    lng = "ST.lang <- Ast.ProgrammingLanguage.Html";
                    break;
                default:
                    lng = "ST.lang <- Ast.ProgrammingLanguage.Unknown";
                    break;
            }

            var inpFileNoExt = Path.GetFileNameWithoutExtension(inpFileName);

            if (!File.Exists(inpFileName))
            {
                Console.Error.WriteLine("Input file {0} does not exist", inpFileName);
                return 1;
            }

            if (File.Exists(outFileName) && File.GetLastWriteTimeUtc(outFileName) > File.GetLastWriteTimeUtc(inpFileName))
            {
                Console.WriteLine("Processing of file '{0}' skiped", inpFileName);
                return 0;
            }

            var functions =
                    from line in File.ReadAllLines(inpFileName).Skip(1)
                    where line.Contains("::=") && !line.Contains("/*nogen*/") && !line.Contains("DEFINITIONS AUTOMATIC TAGS")
                    let declPart = line.Split(':')[0].Trim()
                    let Name = declPart.Split('(')[0].Trim()
                    let Prms = declPart.Split('(')[1].Split(')')[0].Split(',').Select(s => s.Trim()).Where(s => s != "")
                    select new Function { name = Name, prms = Prms };




            using (var txt = new StreamWriter(outFileName))
            {
                txt.WriteLine("module {0}", modName);
                txt.WriteLine("open System");
                txt.WriteLine("open System.Numerics");
                foreach(var md in Uses)
                    txt.WriteLine("open {0}", md);

                txt.WriteLine();
                foreach (var groupedFunc in functions.GroupBy(f => f.ID))
                {
                    foreach (var func in groupedFunc.Take(1))
                    {
                        
                        var prms = func.prms.Select(p => "(\"" + p + "\"," + (p.StartsWith("arr")?p+"|>Seq.toArray":p) + " :>Object)").Join(";");
                        var paramerters =
                                func.prms.Count() > 0 ?
                                func.prms.Select(p => "(" + p + ":" + detectTypeByParam(p) + ")").Join(" ") :
                                "()";
                        if (groupedFunc.Count() == 1)
                        {
                            if (inpFileNoExt != "generic")
                            {
                                txt.WriteLine("let {0} {1} =", func.name, paramerters);
                                txt.WriteLine("    {0}", lng);
                                txt.WriteLine("    ST.call \"{0}\" \"{1}\" [{2}]", inpFileNoExt, func.name, prms);
                            }
                            else
                            {
                                txt.WriteLine("let {0} {1} (fileName:string) =", func.name, paramerters);
                                txt.WriteLine("    {0}", lng);
                                txt.WriteLine("    ST.call {0} \"{1}\" [{2}]", "fileName", func.name, prms);
                            }
                        }
                        else
                        {
                            txt.WriteLine("let {0} {1} codec =", func.name2, paramerters);
                            txt.WriteLine("    {0}", lng);
                            txt.WriteLine("    match codec with");
                            txt.WriteLine("    | Encode    ->");
                            txt.WriteLine("        ST.call \"{0}\" \"{1}\" [{2}]", inpFileNoExt, func.name2 + "_encode", prms);
                            txt.WriteLine("    | Decode    ->");
                            txt.WriteLine("        ST.call \"{0}\" \"{1}\" [{2}]", inpFileNoExt, func.name2 + "_decode", prms);
                        }
                        txt.WriteLine();
                    }
                }
            }
            return 0;
        }
    }


    public static class MyExt
    {
        public static string Join<T>(this IEnumerable<T> pThis, string joiner)
        {
            if (pThis.Any())
                return pThis.Select(x => x.ToString()).Aggregate((cur, next) => cur + joiner + next);
            return "";
        }
    }


}
