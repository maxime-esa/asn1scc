using Daemon.Utils;
using System;
using System.Net;
using System.Timers;

namespace Daemon
{
    class Watchdog
    {
        public Watchdog(int ms)
        {
            timer = new Timer(ms);
            timer.AutoReset = false;
            timer.Elapsed += OnTimerEvent;
        }

        public void BindTo(HttpServer server)
        {
            this.server = server;

            server.InstallHandler("/stayAlive", StayAlive);

            timer.Start();
        }

        private void OnTimerEvent(object source, ElapsedEventArgs e)
        {
            Console.WriteLine("Server stopped by watchdog");
            server.Stop();
        }

        private void StayAlive(HttpListenerContext context)
        {
            timer.Stop();
            timer.Start();
            context.Response.SendPlainText("OK");
        }

        private Timer timer;
        private HttpServer server;
    }
}
