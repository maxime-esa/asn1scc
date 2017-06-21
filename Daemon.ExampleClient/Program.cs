using System;
using System.Net.Http;
using System.Threading.Tasks;

namespace Daemon.ExampleClient
{
    class Program
    {
        static void Main(string[] args)
        {
            var uri = args.Length > 0 ? args[0] : "http://localhost:9749/";
            Run(uri).Wait();
        }

        private async static Task Run(string uri)
        { 
            Console.WriteLine("Asn1Scc Daemon Example Client");

            var client = new HttpClient();
            client.BaseAddress = new Uri(uri);

            var versionResponse = await client.GetAsync("version");
            var version = await versionResponse.Content.ReadAsStringAsync();

            Console.WriteLine("Connected to service version: " + version);
        }
    }
}
