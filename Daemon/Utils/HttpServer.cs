using Daemon.Utils;
using System;
using System.Collections.Generic;
using System.Net;

namespace Daemon.Utils
{
    class HttpServer
    {
        public HttpServer(string uri)
        {
            listener = new HttpListener();

            listener.Prefixes.Add(uri);
        }

        public void Serve()
        { 
            listener.Start();

            while (true)
            {
                HttpListenerContext context = null;
                try
                {
                    context = listener.GetContext();
                    var handler = handlers[context.Request.Url.AbsolutePath];
                    handler.Invoke(context);
                    context.Response.Close();
                    context = null;
                }
                catch (KeyNotFoundException)
                {
                    if (context != null)
                        context.Response.SendError(HttpStatusCode.NotFound);
                }
                catch (Exception)
                {
                    if (context != null)
                        context.Response.SendError(HttpStatusCode.InternalServerError);
                }
            }
        }

        public void InstallHandler(string path, Action<HttpListenerContext> handler)
        {
            handlers[path] = handler;
        }

        private HttpListener listener;
        private Dictionary<string, Action<HttpListenerContext>> handlers = new Dictionary<string, Action<HttpListenerContext>>();
    }
}
