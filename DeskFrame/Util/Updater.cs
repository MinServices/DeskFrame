using System.Diagnostics;
using System.IO;
using System.Text.Json;
using System.Reflection;
using Microsoft.Toolkit.Uwp.Notifications;
using Windows.UI.Notifications;
using System.Net.Http;
using System.Globalization;
using System.Text;
using System.Windows;
using DeskFrame.Properties;
namespace DeskFrame
{
    public class Updater
    {
        private static string _url = "";
        private static string _downloadUrl = "";
        private static string _assetFileName = "";
        private static string tag_name = "";
        private static int updateCount = 0;
        public static async Task CheckUpdateAsync(string url, bool isManualCheck)
        {
            _url = url;
            string currentVersion = Process.GetCurrentProcess().MainModule!.FileVersionInfo.FileVersion!.ToString();
            try
            {
                using (var httpClient = new System.Net.Http.HttpClient())
                {
                    httpClient.DefaultRequestHeaders.UserAgent.Add(new System.Net.Http.Headers.ProductInfoHeaderValue("DeskFrame", currentVersion));
                    var response = await httpClient.GetStringAsync(_url);
                    Debug.WriteLine("got response");
                    using (JsonDocument doc = JsonDocument.Parse(response))
                    {
                        var root = doc.RootElement;
                        string latestVersion = root.GetProperty("tag_name").GetString()!;
                        tag_name = latestVersion;
                        string description = root.GetProperty("body").GetString()!;
                        string published_at = root.GetProperty("published_at").GetString()!;
                        string name = root.GetProperty("name").GetString()!;

                        // Ưu tiên tìm tệp cài đặt .msi, sau đó đến .exe
                        string downloadUrl = "";
                        string assetFileName = "";

                        if (root.TryGetProperty("assets", out JsonElement assetsElement) &&
                            assetsElement.ValueKind == JsonValueKind.Array &&
                            assetsElement.GetArrayLength() > 0)
                        {
                            // Ưu tiên 1: Tệp cài đặt .msi (Windows Installer)
                            foreach (var asset in assetsElement.EnumerateArray())
                            {
                                string aName = asset.GetProperty("name").GetString() ?? "";
                                if (aName.EndsWith(".msi", StringComparison.OrdinalIgnoreCase))
                                {
                                    downloadUrl = asset.GetProperty("browser_download_url").GetString()!;
                                    assetFileName = aName;
                                    break;
                                }
                            }

                            // Ưu tiên 2: Tệp thực thi .exe
                            if (string.IsNullOrEmpty(downloadUrl))
                            {
                                foreach (var asset in assetsElement.EnumerateArray())
                                {
                                    string aName = asset.GetProperty("name").GetString() ?? "";
                                    if (aName.EndsWith(".exe", StringComparison.OrdinalIgnoreCase))
                                    {
                                        downloadUrl = asset.GetProperty("browser_download_url").GetString()!;
                                        assetFileName = aName;
                                        break;
                                    }
                                }
                            }

                            // Fallback: Tệp đầu tiên nếu không khớp đuôi trên
                            if (string.IsNullOrEmpty(downloadUrl))
                            {
                                var firstAsset = assetsElement[0];
                                downloadUrl = firstAsset.GetProperty("browser_download_url").GetString()!;
                                assetFileName = firstAsset.GetProperty("name").GetString() ?? "DeskFrame_Update";
                            }
                        }

                        _downloadUrl = downloadUrl;
                        _assetFileName = assetFileName;

                        string emoji = (name.ToLower().Contains("fix"), name.ToLower().Contains("feature")) switch
                        {
                            (true, true) => "🚀",
                            (true, false) => "🪛", // (screwdriver)
                            (false, true) => "✨",
                            _ => "🚀"
                        };

                        if (IsNewerVersion(latestVersion, currentVersion))
                        {
                            // Có phiên bản mới: Thông báo cho người dùng
                            try
                            {
                                var toastBuilder = new ToastContentBuilder()
                                     .AddText($"{emoji} New release! {name}", AdaptiveTextStyle.Header)
                                     .AddText(description, AdaptiveTextStyle.Body)
                                     .AddButton(new ToastButton()
                                         .SetContent("Cập nhật ngay")
                                         .AddArgument("action", "install_update")
                                         .SetBackgroundActivation())
                                     .AddButton(new ToastButton()
                                         .SetContent("Để sau")
                                         .AddArgument("action", "close")
                                         .SetBackgroundActivation());
                                toastBuilder.Show();
                            }
                            catch (Exception ex)
                            {
                                Debug.WriteLine($"Toast error: {ex.Message}");
                            }

                            // Hiển thị hộp thoại hỏi người dùng cập nhật ngay hoặc để sau
                            System.Windows.Application.Current.Dispatcher.Invoke(async () =>
                            {
                                var result = System.Windows.MessageBox.Show(
                                    $"Tìm thấy phiên bản mới: {name} (Bản hiện tại: v{currentVersion})\n\n{description}\n\nBạn có muốn cập nhật ngay bây giờ không?",
                                    "DeskFrame - Cập nhật",
                                    MessageBoxButton.YesNo,
                                    MessageBoxImage.Information);

                                if (result == MessageBoxResult.Yes)
                                {
                                    await InstallUpdate();
                                }
                            });
                        }
                        else
                        {
                            // Đã là phiên bản mới nhất:
                            // CHỈ hiển thị thông báo khi người dùng chủ động bấm kiểm tra thủ công.
                            // Khi tự động kiểm tra ngầm: TUYỆT ĐỐI KHÔNG BÁO GÌ.
                            if (isManualCheck)
                            {
                                System.Windows.Application.Current.Dispatcher.Invoke(() =>
                                {
                                    System.Windows.MessageBox.Show(
                                        $"Bạn đang sử dụng phiên bản mới nhất (v{currentVersion}).",
                                        "DeskFrame",
                                        MessageBoxButton.OK,
                                        MessageBoxImage.Information);
                                });
                            }
                        }
                    }
                }
                updateCount++;
            }
            catch (Exception e)
            {
                // CHỈ thông báo lỗi khi người dùng bấm kiểm tra thủ công, tránh quấy rầy khi tự động kiểm tra ngầm
                if (isManualCheck)
                {
                    System.Windows.Application.Current.Dispatcher.Invoke(() =>
                    {
                        System.Windows.MessageBox.Show(
                            $"Không thể kiểm tra cập nhật:\n{e.Message}",
                            "DeskFrame - Lỗi",
                            MessageBoxButton.OK,
                            MessageBoxImage.Warning);
                    });
                }
                Debug.WriteLine($"Update error: {e.Message}");
            }
        }

        private static bool IsNewerVersion(string latestTag, string currentVerStr)
        {
            if (string.IsNullOrWhiteSpace(latestTag) || string.IsNullOrWhiteSpace(currentVerStr))
                return false;

            string cleanLatest = latestTag.Trim().TrimStart('v', 'V');
            int dashIdx = cleanLatest.IndexOf('-');
            if (dashIdx > 0) cleanLatest = cleanLatest.Substring(0, dashIdx);

            string cleanCurrent = currentVerStr.Trim().TrimStart('v', 'V');
            dashIdx = cleanCurrent.IndexOf('-');
            if (dashIdx > 0) cleanCurrent = cleanCurrent.Substring(0, dashIdx);

            if (Version.TryParse(cleanLatest, out Version? latestVer) && Version.TryParse(cleanCurrent, out Version? currentVer))
            {
                return latestVer > currentVer;
            }

            return !string.Equals(cleanLatest, cleanCurrent, StringComparison.OrdinalIgnoreCase);
        }

        public static async Task InstallUpdate()
        {
            if (string.IsNullOrEmpty(_downloadUrl))
                return;

            string tag = "update";
            string group = "downloads";

            var toast = new ToastContentBuilder()
                .AddText($"Updating to {tag_name}", AdaptiveTextStyle.Header)
                .AddVisualChild(new AdaptiveProgressBar()
                {
                    Title = $"Progress",
                    Value = new BindableProgressBarValue("progressValue"),
                    ValueStringOverride = new BindableString("progressValueString"),
                    Status = new BindableString("progressStatus")
                })
                .GetToastContent();

            var notif = new ToastNotification(toast.GetXml())
            {
                Tag = tag,
                Group = group
            };
            ToastNotificationManagerCompat.CreateToastNotifier().Show(notif);

            using (var httpClient = new HttpClient())
            using (var response = await httpClient.GetAsync(_downloadUrl, HttpCompletionOption.ResponseHeadersRead))
            {
                response.EnsureSuccessStatusCode();
                var totalBytes = response.Content.Headers.ContentLength ?? -1L;
                var canReportProgress = totalBytes != -1;

                string extension = Path.GetExtension(_assetFileName);
                if (string.IsNullOrEmpty(extension))
                {
                    extension = _downloadUrl.EndsWith(".msi", StringComparison.OrdinalIgnoreCase) ? ".msi" : ".exe";
                }

                string safeTagName = tag_name.Replace('/', '_').Replace('\\', '_');
                string tempFilePath = Path.Combine(Path.GetTempPath(), $"DeskFrame_Update_{safeTagName}{extension}");

                using (var inputStream = await response.Content.ReadAsStreamAsync())
                using (var outputStream = new FileStream(tempFilePath, FileMode.Create, FileAccess.Write, FileShare.None))
                {
                    var buffer = new byte[8192];
                    long totalRead = 0;
                    int read;
                    int lastProgress = -1;

                    while ((read = await inputStream.ReadAsync(buffer, 0, buffer.Length)) > 0)
                    {
                        await outputStream.WriteAsync(buffer, 0, read);
                        totalRead += read;

                        if (canReportProgress)
                        {
                            int progress = (int)(((long)totalRead * 100) / totalBytes);
                            if (progress != lastProgress)
                            {
                                lastProgress = progress;

                                var data = new NotificationData
                                {
                                    SequenceNumber = (uint)progress,
                                    Values =
                                        {
                                            ["progressValue"] = (progress / 100.0).ToString("0.##", CultureInfo.InvariantCulture),
                                            ["progressValueString"] = $"{progress}%",
                                            ["progressStatus"] = "Downloading..."
                                        }
                                };

                                ToastNotificationManagerCompat.CreateToastNotifier().Update(data, tag, group);

                            }
                        }
                    }
                }
                ToastNotificationManagerCompat.CreateToastNotifier().Hide(notif);
                ApplyUpdate(tempFilePath, extension);
            }
        }
        private static bool HasPermissionToWrite(string currentExecutablePath)
        {
            string path = Path.GetDirectoryName(currentExecutablePath)!;
            ProcessStartInfo psi = new ProcessStartInfo
            {
                FileName = "cmd.exe",
                Arguments = $"/C cd /d \"{path}\" && echo. > DeskFrameUpdatePermissionCheck",
                UseShellExecute = false,
                RedirectStandardError = true,
                RedirectStandardOutput = true,
                CreateNoWindow = true
            };

            Process proc = Process.Start(psi)!;
            proc.WaitForExit();
            if (proc.ExitCode == 0)
            {
                Process.Start(new ProcessStartInfo
                {
                    FileName = "cmd.exe",
                    Arguments = $"/C cd /d \"{path}\" && del DeskFrameUpdatePermissionCheck",
                    UseShellExecute = false,
                    CreateNoWindow = true
                });
                return true;
            }
            return false;
        }

        private static void ExecuteCommand(string command, bool needAdmin)
        {
            Debug.WriteLine("Starting CMD...");
            string tempCmd = "";
            if (needAdmin)
            {
                tempCmd = Path.Combine(Path.GetTempPath(), "deskframe_update.cmd");
                File.WriteAllText(tempCmd, command, Encoding.UTF8);
            }
            ProcessStartInfo psi = new ProcessStartInfo
            {
                FileName = needAdmin ? tempCmd : "cmd.exe",
                Arguments = needAdmin ? null : $"/C {command}",
                UseShellExecute = needAdmin,
                CreateNoWindow = true,
                WindowStyle = ProcessWindowStyle.Hidden,
                Verb = needAdmin ? "runas" : ""
            };
            Process.Start(psi);
        }

        private static void ApplyUpdate(string tempPath, string extension)
        {
            string currentExecutablePath = Process.GetCurrentProcess().MainModule!.FileName;
            bool isMsi = extension.Equals(".msi", StringComparison.OrdinalIgnoreCase);

            if (isMsi)
            {
                string updateScript = Path.Combine(Path.GetTempPath(), "deskframe_msi_update.cmd");
                string scriptContent =
                    "@echo off\r\n" +
                    "timeout /t 1 /nobreak >nul\r\n" +
                    "taskkill /F /IM DeskFrame.exe /T >nul 2>&1\r\n" +
                    $"start /wait msiexec.exe /i \"{tempPath}\" /passive\r\n" +
                    "timeout /t 1 /nobreak >nul\r\n" +
                    $"start \"\" \"{currentExecutablePath}\" --updated\r\n" +
                    "exit\r\n";

                File.WriteAllText(updateScript, scriptContent, Encoding.UTF8);

                ProcessStartInfo psi = new ProcessStartInfo
                {
                    FileName = updateScript,
                    UseShellExecute = true,
                    CreateNoWindow = true,
                    WindowStyle = ProcessWindowStyle.Hidden,
                    Verb = "runas"
                };

                try
                {
                    Process.Start(psi);
                    Environment.Exit(0);
                }
                catch (Exception ex)
                {
                    Debug.WriteLine($"User canceled elevation or error launching MSI updater: {ex.Message}");
                    Process.Start(new ProcessStartInfo(tempPath) { UseShellExecute = true });
                    Environment.Exit(0);
                }
            }
            else
            {
                string command = $"timeout /t 1 /nobreak >nul & taskkill /F /IM DeskFrame.exe /T >nul 2>&1 & move /y \"{tempPath}\" \"{currentExecutablePath}\" & start \"\" \"{currentExecutablePath}\" --updated & exit";

                if (HasPermissionToWrite(currentExecutablePath))
                {
                    ExecuteCommand(command, false);
                    Environment.Exit(0);
                }
                else
                {
                    var dialog = new Wpf.Ui.Controls.MessageBox
                    {
                        Title = "DeskFrame",
                        Content = Lang.Deskframe_Update_DialogContent,
                        PrimaryButtonText = "OK"
                    };

                    var result = dialog.ShowDialogAsync();

                    if (result.Result == Wpf.Ui.Controls.MessageBoxResult.Primary)
                    {
                        ExecuteCommand(command, true);
                        Environment.Exit(0);
                    }
                }
            }
        }
    }
}
