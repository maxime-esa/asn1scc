using Service.Dto;
using System;
using System.IO;

namespace Service.Implementation.Utils
{
    class TemporaryDirectory : IDisposable
    {
        public string Path { get; }

        public TemporaryDirectory()
        {
            Path = System.IO.Path.Combine(System.IO.Path.GetTempPath(), System.IO.Path.GetRandomFileName());
            Directory.CreateDirectory(Path);
        }

        protected virtual void Dispose(bool disposing)
        {
            Directory.Delete(Path, recursive: true);
        }

        ~TemporaryDirectory()
        {
            Dispose(false);
        }

        public void Dispose()
        {
            Dispose(true);
            GC.SuppressFinalize(this);
        }

        public string FullPath(string fileName)
        {
            return System.IO.Path.Combine(Path, fileName);
        }

        public string Store(FileData file)
        {
            var filePath = FullPath(file.Name);
            File.WriteAllText(filePath, file.Contents);
            return filePath;
        }
    }
}
