using Daemon.Utils;
using Service;
using Service.Dto;
using System.Net;

namespace Daemon
{
    class Asn1ServiceBindings
    {
        public Asn1ServiceBindings(IAsn1Service service)
        {
            this.service = service;
        }

        public void BindTo(HttpServer server)
        {
            server.InstallHandler("version", GetVersion);
            server.InstallHandler("ast", BuildAst);
        }

        private void GetVersion(HttpListenerContext context)
        {
            context.Response.SendPlainText(service.GetVersion());
        }

        private void BuildAst(HttpListenerContext context)
        {
            var data = context.Request.ReadJson<InputFiles>();
            context.Response.SendJson(service.BuildAst(data));
        }

        private IAsn1Service service;
    }
}
