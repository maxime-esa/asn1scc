using Service.Dto;
using Service.Implementation.Utils;
using System;
using System.IO;
using System.Linq;

namespace Service.Implementation
{
    public class Asn1Service : IAsn1Service
    {
        public string BuildAst(Files files)
        {
            using (var dir = new TemporaryDirectory())
            {
                var asnPaths = files.AsnFiles.Select(f => dir.Store(f));
                var outFile = dir.FullPath("AST.xml");

                var args = new[] { "-ast", outFile };

                lock (asn1f2AccessLock)
                {
                    Asn1f2.Program.Main(args.Concat(asnPaths).ToArray());
                }

                var lines = File.ReadAllLines(outFile).Select(l => l.Replace(dir.Path, "")).ToArray();
                return String.Join("\n", lines);
            }
        }

        public string GetVersion()
        {
            return Asn1f2.Program.GetVersionString();
        }

        private object asn1f2AccessLock = new object();
    }
}
