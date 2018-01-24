using System.Collections.Generic;

namespace Service.Dto
{
    public class Output
    {
        public int ErrorCode { get; set; }
        public IEnumerable<FileData> Files { get; set; }
        public IEnumerable<string> Messages { get; set; }
    }
}
