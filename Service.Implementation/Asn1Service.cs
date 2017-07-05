using Antlr.Asn1;
using Service.Dto;
using Service.Implementation.Utils;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Service.Implementation
{
    public class Asn1Service : IAsn1Service
    {
        public Output BuildAst(InputFiles files)
        {
            using (var dir = new TemporaryDirectory())
            {
                var xmlFileName = "AST.xml";

                try
                {
                    lock (asn1f2AccessLock)
                    {
                        var exitCode = Asn1f2.Program.CheckSuccess(BuildAstArguments(dir.FullPath(xmlFileName),
                                                                                     StoreFilesInDirectory(dir, files)));
                        if (exitCode != 0)
                            return new Output() { ErrorCode = exitCode, Messages = new[] { "Internal compiler error" } };
                    }
                }
                catch (asn1Parser.SyntaxErrorException ex)
                {
                    return new Output() { ErrorCode = 1, Messages = new[] { ex.Message } };
                }
                catch (FsUtils.SemanticError ex)
                {
                    return new Output() { ErrorCode = 2, Messages = new[] { Asn1f2.Program.FormatError(ex) } };
                }

                return new Output() { ErrorCode = 0, Files = new[] { ReadAstXmlFromTempDir(xmlFileName, dir) } };
            }
        }

        private FileData ReadAstXmlFromTempDir(string file, TemporaryDirectory dir)
        {
            var lines = File.ReadAllLines(dir.FullPath(file)).Select(l => l.Replace(dir.Path, ""));
            return new FileData() { Name = file, Contents = String.Join("\n", lines.ToArray()) };
        }

        private string[] BuildAstArguments(string outFile, IEnumerable<string> inputPaths)
        {
            var args = new[] { "-ast", outFile };
            return args.Concat(inputPaths).ToArray();
        }

        private IEnumerable<string> StoreFilesInDirectory(TemporaryDirectory dir, InputFiles input)
        {
            return input.AsnFiles.Select(f => dir.Store(f));
        }

        public string GetVersion()
        {
            return Asn1f2.Program.GetVersionString();
        }

        private object asn1f2AccessLock = new object();
    }
}
