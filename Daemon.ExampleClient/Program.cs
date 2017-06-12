using Service.Dto;
using System;
using System.Net.Http;

namespace Daemon.ExampleClient
{
    class Program
    {
        static void Main(string[] args)
        {
            var uri = args.Length > 0 ? args[0] : "http://localhost:9749/";
            Run(uri);
        }

        private async static void Run(string uri)
        { 
            Console.WriteLine("Asn1Scc Daemon Example Client");

            using (var client = new HttpClient())
            {
                using (var versionResponse = await client.GetAsync(uri + "/version"))
                using (var content = versionResponse.Content)
                {
                    var version = await content.ReadAsStringAsync();
                    Console.WriteLine("Connected to service version: " + version);
                }
            }
        }
    }
}
