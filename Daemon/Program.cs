using Daemon.Utils;
using Service.Implementation;
using System;

namespace Daemon
{
    class Program
    {
        static void Main(string[] args)
        {
            var uri = args.Length > 0 ? args[0] : "http://localhost:9749/";

            Console.WriteLine("Asn1Scc Daemon listening on: " + uri);

            var bindings = new Asn1ServiceBindings(new Asn1Service());

            var server = new HttpServer(uri);

            bindings.BindTo(server);

            server.Serve();
            // TODO nice closing of service?
        }
    }
}
