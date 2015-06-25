using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Antlr.Runtime;
using Antlr.Runtime.Tree;
using System.IO;
using Antlr.Asn1;
using Antlr.Acn;


namespace Asn1f2
{
    public class Program
    {
        static int Main(string[] args)
        {
            if (System.Diagnostics.Debugger.IsAttached)
                return Main2(args);
            try
            {
                return Main2(args);
            }
            catch (FsUtils.BugErrorException ex)
            {
                Console.Error.WriteLine("*****************************************************************************");
                Console.Error.WriteLine("* A fatal error has occurred");
                Console.Error.WriteLine("* Unexpected internal compiler error");
                Console.Error.WriteLine("*");
                Console.Error.WriteLine("* ");
                Console.Error.WriteLine("* Please report bugs to: support@semantix.gr");
                Console.Error.WriteLine("* Error is:");
                Console.Error.WriteLine("* {0}", ex.Data0);
                Console.Error.WriteLine("* ");
                Console.Error.WriteLine("* Call stack is:");
                Console.Error.WriteLine("* ");
                foreach (var l in ex.StackTrace.Split('\n'))
                    Console.Error.WriteLine(l.Replace("\r", ""));
                Console.Error.WriteLine("*****************************************************************************");

                return 3;
            }
            catch (Exception ex)
            {
                Console.Error.WriteLine(ex.Message);
                return 3;
            }

        }
        static int Main2(string[] args)
        {
            try
            {

                int ret = CheckSuccess(args);
                if (ret != 0)
                    return ret;
            }
            catch (asn1Parser.SyntaxErrorException ex)
            {
                Console.Error.WriteLine(ex.Message);
                return 1;
            }
            catch (FsUtils.SemanticError ex)
            {
                if (ex.Data0.Equals(FsUtils.emptyLocation))
                    // do not display empty file/zero line for "emptyLocation"
                    Console.Error.WriteLine("{0}", ex.Data1);
                else
                    Console.Error.WriteLine("File:{0}, line:{1}, {2}", Path.GetFileName(ex.Data0.srcFilename), ex.Data0.srcLine, ex.Data1);
                return 2;
            }

            return 0;

        }



        public static int CheckSuccess(IEnumerable<string> args)
        {
            var asn1InputFiles = args.Where(a => !a.StartsWith("-") && (a.ToLower().EndsWith(".asn1") || a.ToLower().EndsWith(".asn")));
            var acnInputFiles = args.Where(a => !a.StartsWith("-") && a.ToLower().EndsWith(".acn"));
            
            foreach (var f in asn1InputFiles.Concat(acnInputFiles))
                if (!File.Exists(f))
                    throw new FsUtils.SemanticError(new FsUtils.SrcLoc(f, 0, 0), string.Format("File does not exist"));

            var cmdArgs = CmdLineArgs.CmdLineArguments.GetInstance(Usage);
            CmdLineArgs.CmdLineArguments.Args = args.ToArray();
            cmdArgs.RegisterArg(new List<CmdLineArgs.CmdArg>() 
            { 
                new CmdLineArgs.CmdArg { HasValue = false, Name = "equal", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = false, Name = "c", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = false, Name = "Ada", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = false, Name = "uPER", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = false, Name = "ACN", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = false, Name = "ACND", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = false, Name = "XER", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = false, Name = "BER", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = true, Name = "o", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = true, Name = "wordSize", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = true, Name = "ast", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = true, Name = "customStg", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = true, Name = "customStgAstVerion", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = true, Name = "icdUper", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = true, Name = "icdAcn", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = false, Name = "vc", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = false, Name = "debug", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = true, Name = "typePrefix", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = false, Name = "help", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = false, Name = "atc", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = false, Name = "oss", Madatory=false}, 
                new CmdLineArgs.CmdArg { HasValue = false, Name = "AdaUses", Madatory=false}, 
            });
            cmdArgs.CheckArguments();
            if (cmdArgs.HasArgument("h"))
                Environment.Exit(Usage());
            if (!asn1InputFiles.Any())
            {
                Console.Error.WriteLine("No input files");
                Environment.Exit(Usage());
            }
            var generateEqualFunctions = cmdArgs.HasArgument("equal") || cmdArgs.HasArgument("atc");
            var outDir = cmdArgs.GetOptionalArgument("o") ?? ".";
            var bGenerateAcnDefault = cmdArgs.HasArgument("ACND");

            var ws = cmdArgs.GetOptionalArgument("wordSize", "8");
            if (ws != "8")
            {
                Console.Error.WriteLine("Invalid argument wordSize");
                return 4;
            }

            if (!Directory.Exists(outDir))
            {
                Console.Error.WriteLine("Output directory '{0}' does not exist", outDir);
                return 4;
            }

            bool bDebug = cmdArgs.HasArgument("debug");
            List<ParameterizedAsn1Ast.Asn1Encoding> encodings = new List<ParameterizedAsn1Ast.Asn1Encoding>();
            if (cmdArgs.HasArgument("uPER"))
                encodings.Add(ParameterizedAsn1Ast.Asn1Encoding.UPER);
            if (cmdArgs.HasArgument("ACN"))
                encodings.Add(ParameterizedAsn1Ast.Asn1Encoding.ACN);
            if (cmdArgs.HasArgument("XER"))
                encodings.Add(ParameterizedAsn1Ast.Asn1Encoding.XER);
            if (cmdArgs.HasArgument("BER"))
                encodings.Add(ParameterizedAsn1Ast.Asn1Encoding.BER);

            var asn1Files = ParseAsn1InputFiles(asn1InputFiles);
            var astXmlFile = cmdArgs.GetOptionalArgument("ast", "");
            var customStg = cmdArgs.GetOptionalArgument("customStg", "");


            var icdUperHtmlFileName = cmdArgs.GetOptionalArgument("icdUper", "");
            if (!String.IsNullOrEmpty(icdUperHtmlFileName) && !(icdUperHtmlFileName.ToLower().EndsWith(".html") || icdUperHtmlFileName.ToLower().EndsWith(".htm")))
            {
                Console.Error.WriteLine("Invalid output filename '{0}'\nGenerated icd files must have an .html or .htm extension", icdUperHtmlFileName);
                return 4;
            }

            var icdAcnHtmlFileName = cmdArgs.GetOptionalArgument("icdAcn", "");
            if (!String.IsNullOrEmpty(icdAcnHtmlFileName) && !(icdAcnHtmlFileName.ToLower().EndsWith(".html") || icdAcnHtmlFileName.ToLower().EndsWith(".htm")))
            {
                Console.Error.WriteLine("Invalid output filename '{0}'\nGenerated icd files must have an .html or .htm extension", icdAcnHtmlFileName);
                return 4;
            }


            var asn1Ast0 = MapParamAstToNonParamAst.DoWork(CreateAsn1AstFromAntlrTree.CreateAstRoot(asn1Files, encodings.ToArray(),
                    generateEqualFunctions, cmdArgs.GetOptionalArgument("typePrefix", ""), cmdArgs.HasArgument("oss"),
                    astXmlFile, icdUperHtmlFileName, icdAcnHtmlFileName));

            CheckAsn1.CheckFiles(asn1Ast0);

            if (astXmlFile != "")
            {

                XmlAst.DoWork(EnsureUniqueEnumNames.DoWork(asn1Ast0));
                return 0;
            }


            var acnAstUnresolved = AcnCreateFromAntlr.CreateAcnAst(ParseAcnInputFiles(acnInputFiles), asn1Ast0);
           

            //PrintAsn1.DoWork(asn1Ast0, outDir, ".0.asn1");
            //PrintAsn1.AcnPrint.print_AcnAst(acnAstUnresolved, "a_acn.raw.txt");
            var asn1Ast = UpdateAcnProperties.DoWork(asn1Ast0, acnAstUnresolved).Item1;
            var acnAstResolved = Acn.Resolve.ResolveRelativePaths(acnAstUnresolved, asn1Ast);

            //PrintAsn1.DebugPrintAsn1Acn(asn1Ast, acnAstResolved, ".", ".1.asn1");
            var noInnerasn1Ast = ReplaceInnerTypes.DoWork(RemoveNumericStrings.DoWork(asn1Ast), acnAstResolved, false);
            //PrintAsn1.DebugPrintAsn1Acn(noInnerasn1Ast.Item1, noInnerasn1Ast.Item2, ".", ".1b.asn1");

            var refTypesWithNoConstraints_asn1_acn = RemoveConstraintsFromRefTypes.DoWork(noInnerasn1Ast.Item1, noInnerasn1Ast.Item2);

            var refTypesWithNoConstraints = refTypesWithNoConstraints_asn1_acn.Item1;
            var acnAst2 = refTypesWithNoConstraints_asn1_acn.Item2;

            //PrintAsn1.DebugPrintAsn1Acn(refTypesWithNoConstraints, acnAst2, ".", ".2.asn1");
            RemoveConstraintsFromRefTypes.CheckReferences(refTypesWithNoConstraints, acnAst2);

            var acnAst3 = Acn.RemoveVirtualPaths(refTypesWithNoConstraints, acnAst2);
            
            //last validation check, it may throw a SemanticException
            Acn.CheckForUnreferencedAcnInsertedFields(refTypesWithNoConstraints, acnAst3);
            
            if (!RemoveConstraintsFromRefTypes.CheckReferences(refTypesWithNoConstraints, acnAst3))
            {
                throw new FsUtils.BugErrorException("Broken paths");
            }
            if (bDebug) PrintAsn1.DebugPrintAsn1Acn(refTypesWithNoConstraints, acnAst3, outDir, ".3.asn1");

            var bGenTestCases = cmdArgs.HasArgument("atc");

            if (customStg != "")
            {
                var files = customStg.Split(':');
                if (files.Length != 2)
                {
                    files = customStg.Split(new string[] { "::" }, StringSplitOptions.RemoveEmptyEntries);
                    if (files.Length != 2)
                    {
                        Console.Error.WriteLine("Invalid usage of customStg argument. Please use ':' to seperate the stg file with output file");
                        Console.Error.WriteLine("E.g. -customStg mystg.stg:output.txt ");
                        Console.Error.WriteLine("Under windows, you may user double :: to separate the stg file with output file");
                        Console.Error.WriteLine("E.g. -customStg c:\\mystg.stg::c:\\output.txt ");
                        return 4;
                    }
                }
                var stgFileName = files.First();
                var outFileName = files.Last();
                if (!File.Exists(stgFileName))
                {
                    Console.Error.WriteLine("Custom stg file '{0}' does not exist", stgFileName);
                    return 4;
                }

                var customStgAstVer = cmdArgs.GetOptionalArgument("customStgAstVerion", "1");

                var astForCustomBackend = asn1Ast0;
                if (customStgAstVer == "1")
                    astForCustomBackend = asn1Ast0;
                else if (customStgAstVer == "2")
                    astForCustomBackend = noInnerasn1Ast.Item1;
                else if (customStgAstVer == "3")
                    astForCustomBackend = refTypesWithNoConstraints;
                else if (customStgAstVer == "4")
                    astForCustomBackend = EnsureUniqueEnumNames.DoWork(refTypesWithNoConstraints);
                else
                {
                    Console.Error.WriteLine("Invalid value of customStgAstVerion argument.\nPlease provide one of the following values:");
                    Console.Error.WriteLine("\t1\t==> Ast version where parameterized types have been removed");
                    Console.Error.WriteLine("\t2\t==> Ast version where inner types have been removed");
                    Console.Error.WriteLine("\t3\t==> Ast version where contraint reference types have been removed");
                    Console.Error.WriteLine("\t4\t==> Ast version where Enumerated names are unique (required by C backend)");
                    return 4;
                }

                genericBackend.DoWork(astForCustomBackend, Path.GetFileNameWithoutExtension(stgFileName), outFileName);
            }


            if (cmdArgs.HasArgument("Ada"))
            {
                var astForBackend = EnsureUniqueEnumNames.DoWork(refTypesWithNoConstraints);

                spark_body.DoWork(astForBackend, acnAst3, outDir);

                if (bGenTestCases)
                {
                    var vas = "ALL";

                    spark_automatic_test_cases.CreateTestCases(astForBackend, acnAst3, outDir);
                    spark_main.CreateMainFile(astForBackend, acnAst3, outDir, vas);
                    spark_main.CreateMakeFile(astForBackend, outDir);
                }

                WriteTextFile(Path.Combine(outDir, spark_body.GetRTLName() + ".adb"), Resource1.adaasn1rtl_adb);
                WriteTextFile(Path.Combine(outDir, spark_body.GetRTLName() + ".ads"), Resource1.adaasn1rtl_ads);
                WriteTextFile(Path.Combine(outDir, "IgnoredExaminerWarnings.wrn"), Resource1.IgnoredExaminerWarnings);
                WriteTextFile(Path.Combine(outDir, "gnat.cfg"), Resource1.gnat);
                WriteTextFile(Path.Combine(outDir, "runSpark.sh"), Resource1.run);
                WriteTextFile(Path.Combine(outDir, "GPS_project.gpr"), Resource1.GPS_project);

                spark_main.CreateSparkIndexFile(astForBackend, bGenTestCases, outDir);

                System.IO.Directory.CreateDirectory(Path.Combine(outDir, "examiner"));
                System.IO.Directory.CreateDirectory(Path.Combine(outDir, "bin"));
            }
            /*else */if (cmdArgs.HasArgument("c"))
            {
                WriteTextFile(Path.Combine(outDir, "asn1crt.c"), Resource1.asn1crt);
                WriteTextFile(Path.Combine(outDir, "asn1crt.h"), Resource1.asn1crt1);
                WriteTextFile(Path.Combine(outDir, "acn.c"), Resource1.Acn);
                WriteTextFile(Path.Combine(outDir, "real.c"), Resource1.real);
                WriteTextFile(Path.Combine(outDir, "ber.c"), Resource1.ber);
                WriteTextFile(Path.Combine(outDir, "xer.c"), Resource1.xer);

                var astForBackend = EnsureUniqueEnumNames.DoWork(refTypesWithNoConstraints);
                c_body.DoWork(astForBackend, acnAst3, outDir);

                if (bGenTestCases)
                {
                    var vas = "ALL";

                    automatic_test_cases.CreateTestCases(astForBackend, acnAst3, outDir);
                    automatic_test_cases.CreateMainFile(astForBackend, acnAst3, outDir, vas);
                    automatic_test_cases.CreateMakeFile(astForBackend, acnAst3, outDir);
                }

            }
            /*else */if (bGenerateAcnDefault)
            {
                c_body.EmmitDefaultACNGrammar(asn1Ast0, outDir);
            }
            /*else */
            {
                if (cmdArgs.HasArgument("AdaUses"))
                    foreach (var s in Ast.AdaUses(refTypesWithNoConstraints))
                        Console.WriteLine(s);

                if (cmdArgs.HasArgument("icdUper"))
                {
                    var noInnerasn1Ast2 = ReplaceInnerTypes.DoWork(asn1Ast, acnAstResolved, true);
                    icdUper.DoWork(noInnerasn1Ast2.Item1, acnAst3, outDir);
                }
                if (cmdArgs.HasArgument("icdAcn"))
                {
                    var noInnerasn1Ast2 = ReplaceInnerTypes.DoWork(asn1Ast, acnAstResolved, true);
                    icdAcn.DoWork(noInnerasn1Ast2.Item1, acnAstResolved, outDir);
                }
                
            }

            return 0;
        }


        public static List<Tuple<ITree, string, IToken[]>> ParseAsn1InputFiles(IEnumerable<string> inputFiles)
        {
            var parsedInputFiles = new List<Tuple<ITree, string, IToken[]>>();

            foreach (var inFileName in inputFiles)
            {
                ICharStream input = new ANTLRFileStream(inFileName);
                asn1Lexer lexer = new asn1Lexer(input);
                CommonTokenStream tokens = new CommonTokenStream(lexer);

                List<IToken> tokenslst = new List<IToken>();
                foreach (IToken token in tokens.GetTokens())
                {
                    tokenslst.Add(token);
                }

                asn1Parser parser = new asn1Parser(tokens);
                asn1Parser.moduleDefinitions_return result = parser.moduleDefinitions();

                ITree tree = (CommonTree)result.Tree;
                CommonTreeNodeStream nodes = new CommonTreeNodeStream(tree);
                nodes.TokenStream = tokens;
                parsedInputFiles.Add(Tuple.Create(tree, inFileName, tokenslst.ToArray() ));
            }

            return parsedInputFiles;
        }

        public static List<Tuple<ITree, string, IToken[]>> ParseAcnInputFiles(IEnumerable<string> inputFiles)
        {
            var parsedInputFiles = new List<Tuple<ITree, string, IToken[]>>();

            foreach (var inFileName in inputFiles)
            {
                ICharStream input = new ANTLRFileStream(inFileName);
                acnLexer lexer = new acnLexer(input);
                CommonTokenStream tokens = new CommonTokenStream(lexer);

                List<IToken> tokenslst = new List<IToken>();
                foreach (IToken token in tokens.GetTokens())
                {
                    tokenslst.Add(token);
                }

                acnParser parser = new acnParser(tokens);
                acnParser.moduleDefinitions_return result = parser.moduleDefinitions();

                ITree tree = (CommonTree)result.Tree;
                CommonTreeNodeStream nodes = new CommonTreeNodeStream(tree);
                nodes.TokenStream = tokens;
                parsedInputFiles.Add(Tuple.Create(tree, inFileName, tokenslst.ToArray()));
            }

            return parsedInputFiles;
        }

        static int Usage()
        {
            var procName = "asn1";
            Console.Error.WriteLine();
            Console.Error.WriteLine("Semantix ASN.1 Compiler");
            Console.Error.WriteLine("Current Version is: 3.2.{0} ", Svn.Version);
            Console.Error.WriteLine("Usage:");
            Console.Error.WriteLine();
            Console.Error.WriteLine("{0}  <OPTIONS> file1, file2, ..., fileN ", procName);
            Console.Error.WriteLine();
            Console.Error.WriteLine("Where OPTIONS are:\n\n");
            Console.Error.WriteLine("\t -c\t\t\tgenerate code for the C/C++ programming language");
            Console.Error.WriteLine("\t -Ada\t\t\tgenerate code for the Ada/SPARK programming language");
            Console.Error.WriteLine("\t -uPER\t\t\tgenerates encoding and decoding functions for");
            Console.Error.WriteLine("\t\t\t\tunaligned Packed Encoding Rules (uPER)");
            Console.Error.WriteLine("\t -ACN\t\t\tgenerates encoding and decoding functions using");
            Console.Error.WriteLine("\t\t\t\tthe ASSERT ASN.1 encoding Control Notation");
            Console.Error.WriteLine("\t -ACND\t\t\tcreates ACN grammars for the input ASN.1 grammars");
            Console.Error.WriteLine("\t\t\t\tusing the default encoding properties");
            //Console.Error.WriteLine("\t -BER\t\t\tgenerates encoding and decoding functions for.");
            //Console.Error.WriteLine("\t\t\t\tBasic Encoding Rules (BER)");
            //Console.Error.WriteLine();
            //Console.Error.WriteLine("\t -XER\t\t\tgenerates encoding and decoding functions for");
            //Console.Error.WriteLine("\t\t\t\tXML Encoding Rules");
            //Console.Error.WriteLine();
            Console.Error.WriteLine("\t -ast file.xml          Produces an XML file of the parsed input ASN.1");
            Console.Error.WriteLine("\t\t\t\tgrammar.(No encoders/decoders are produced)");
            Console.Error.WriteLine("\t -customStg stgFile.stg:outputFile");
            Console.Error.WriteLine("\t\t\t\tInvokes the custom stg file 'stgFile.stg' and produces the");
            Console.Error.WriteLine("\t\t\t\toutput file 'outputFile'");
            Console.Error.WriteLine("\t -customStgAstVerion astVersionNumber");
            Console.Error.WriteLine("\t\t\t\twhere astVersionNumber is:");
            Console.Error.WriteLine("\t\t\t\t1\tparameterized types have been removed");
            Console.Error.WriteLine("\t\t\t\t2\tinner types have been removed");
            Console.Error.WriteLine("\t\t\t\t3\tconstraint reference types have been removed");
            Console.Error.WriteLine("\t\t\t\t4\tEnumerated names are unique (required by C backend)");
            Console.Error.WriteLine("\t -icdUper file.html     Produces an Interface Control Document for");
            Console.Error.WriteLine("\t\t\t\tthe input ASN.1 grammar for uPER encoding");
            Console.Error.WriteLine("\t -icdAcn file.html      Produces an Interface Control Document for ");
            Console.Error.WriteLine("\t\t\t\tthe input ASN.1 and ACN grammars for ACN encoding");
            Console.Error.WriteLine("\t -typePrefix prefix\tadds 'prefix' to all generated C or Ada/SPARK data types.");
            Console.Error.WriteLine("\t -o outdir\t\tdirectory where all files are produced.");
            Console.Error.WriteLine("\t\t\t\tDefault is current directory");
            Console.Error.WriteLine("\t -atc\t\t\tcreate automatic test cases.");
            Console.Error.WriteLine("\t\t\t\tDefault is current directory");
            Console.Error.WriteLine("\t -equal \t\tGenerate functions for testing type equality");
            Console.Error.WriteLine("\t\t\t\tWhen using Ada, compiler must support Ada2012");
            Console.Error.WriteLine();
            Console.Error.WriteLine();
            Console.Error.WriteLine("Example:");
            Console.Error.WriteLine();
            Console.Error.WriteLine("\t{0} -Ada -uPER MyFile.asn", procName);
            return 4;
        }

        public static void WriteTextFile(string fileName, string data, bool makeItExecutable=false)
        {
            System.IO.File.WriteAllText(fileName, data.Replace("\r",""));

            if (makeItExecutable)
            {
                try
                {
                    File.SetAttributes(fileName, (FileAttributes)( (uint)File.GetAttributes(fileName) | 0x80000000));
                }
                catch (Exception)
                {
                }
            }
        }
    }
}
