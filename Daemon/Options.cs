using CommandLine;
using CommandLine.Text;
using Service.Implementation;

namespace Daemon
{
    public class Options
    {
        [Option('u', "uri",
                HelpText = "URI on which server should listen.",
                DefaultValue = "http://localhost:9749/")]
        public string Uri { get; set; }

        [HelpOption]
        public string GetUsage()
        {
            var help = new HelpText
            {
                Heading = new HeadingInfo("ASN1SCC Daemon", new Asn1Service().GetVersion()),
                AddDashesToOption = true
            };
            // TODO: help.AddPreOptionsLine("<<license details here.>>");
            help.AddOptions(this);
            return help;
        }
    }
}
