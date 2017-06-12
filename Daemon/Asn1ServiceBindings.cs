using Daemon.Utils;
using Service;
using Service.Dto;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Net;
using System.Text;
using System.Threading.Tasks;

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
            server.InstallHandler("/version", (c) => GetVersion(c));
            server.InstallHandler("/ast", (c) => BuildAst(c));
        }

        private void GetVersion(HttpListenerContext context)
        {
            context.Response.SendJson(service.GetVersion());
        }

        private void BuildAst(HttpListenerContext context)
        {
            var data = context.Request.ReadJson<Files>();
            context.Response.SendJson(service.BuildAst(data));
        }

        private IAsn1Service service;
    }
}
